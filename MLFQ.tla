-------------------------------- MODULE MLFQ --------------------------------

EXTENDS Integers, Sequences

Processors == {"p1","p2"}
Tasks == {"t1","t2","t3","t4"}
TimeQuanta1 == 5
TimeQuanta2 == 3
TimeQuanta3 == 1
BurstTimes == [t1 |-> 7, t2 |-> 4, t3 |-> 2, t4 |-> 5]

VARIABLES queue1, queue2, queue3, taskStatus, taskRemainingTime, clock, processorStatus, taskProcessorMap, processorTimeLeft

vars == <<queue1, queue2, queue3, taskStatus, taskRemainingTime, clock, processorStatus, taskProcessorMap, processorTimeLeft>>

TypeOK ==
        /\ taskStatus \in {"waiting", "executing", "done"}
        /\ processorStatus \in {"busy", "free" }  

Init ==
    /\ queue1 = <<"t1","t4">>
    /\ queue2 = <<"t2">>
    /\ queue3 = <<"t3">>
    /\ taskStatus = [t \in Tasks |-> "waiting"]
    /\ processorStatus = [ p \in Processors |-> "free"]
    /\ taskProcessorMap = [ p \in Processors |-> "none"]
    /\ processorTimeLeft = [ p \in Processors |-> 0]
    /\ taskRemainingTime = [ t \in Tasks |-> BurstTimes[t]]
    /\ clock = 0

ExecuteTask ==
    \E p \in Processors :
        /\ processorStatus[p] = "free"
        /\ IF Len(queue1) > 0 /\ taskStatus[Head(queue1)] = "waiting"
           THEN /\ taskProcessorMap' = [taskProcessorMap EXCEPT ![p] = Head(queue1)]
                /\ processorTimeLeft' = [processorTimeLeft EXCEPT ![p] = TimeQuanta1]
                /\ queue1' = Tail(queue1)
                /\ queue2' = queue2
                /\ queue3' = queue3
                /\ taskStatus' = [taskStatus EXCEPT ![Head(queue1)] = "executing"]
                /\ processorStatus' = [processorStatus EXCEPT ![p] = "busy"]
           ELSE IF Len(queue2) > 0 /\ taskStatus[Head(queue2)] = "waiting"
                THEN /\ taskProcessorMap' = [taskProcessorMap EXCEPT ![p] = Head(queue2)]
                     /\ processorTimeLeft' = [processorTimeLeft EXCEPT ![p] = TimeQuanta2]
                     /\ queue1' = queue1
                     /\ queue2' = Tail(queue2)
                     /\ queue3' = queue3
                     /\ taskStatus' = [taskStatus EXCEPT ![Head(queue2)] = "executing"]
                     /\ processorStatus' = [processorStatus EXCEPT ![p] = "busy"]
                ELSE IF Len(queue3) > 0 /\ taskStatus[Head(queue3)] = "waiting"
                     THEN /\ taskProcessorMap' = [taskProcessorMap EXCEPT ![p] = Head(queue3)]
                          /\ processorTimeLeft' = [processorTimeLeft EXCEPT ![p] = TimeQuanta3]
                          /\ queue1' = queue1
                          /\ queue2' = queue2
                          /\ queue3' = Tail(queue3)
                          /\ taskStatus' = [taskStatus EXCEPT ![Head(queue3)] = "executing"]
                          /\ processorStatus' = [processorStatus EXCEPT ![p] = "busy"]
                     ELSE /\ UNCHANGED << queue1, queue2, queue3, taskProcessorMap, processorTimeLeft, taskStatus, processorStatus >>
        /\ UNCHANGED << taskRemainingTime, clock >>


PreemptTask ==
    \E p \in Processors, t \in Tasks :
        /\ processorTimeLeft[p] = 0
        /\ taskProcessorMap[p] = t
        /\ taskStatus[t] = "executing"
        /\ IF taskRemainingTime[t] > TimeQuanta1
           THEN /\ queue1' = Append(queue1, t)
                /\ queue2' = queue2
                /\ queue3' = queue3
           ELSE IF taskRemainingTime[t] > TimeQuanta2
                THEN /\ queue1' = queue1
                     /\ queue2' = Append(queue2, t)
                     /\ queue3' = queue3
                ELSE /\ queue1' = queue1
                     /\ queue2' = queue2
                     /\ queue3' = Append(queue3, t)
        /\ taskStatus' = [taskStatus EXCEPT ![t] = "waiting"]
        /\ processorStatus' = [processorStatus EXCEPT ![p] = "free"]
        /\ taskProcessorMap' = [taskProcessorMap EXCEPT ![p] = "none"]
        /\ UNCHANGED << taskRemainingTime, clock, processorTimeLeft >>
 
 RemoveTask ==
    \E t \in Tasks :
        /\ taskRemainingTime[t] = 0
        /\ taskStatus[t] = "executing"
        /\ \E p \in Processors : taskProcessorMap[p] = t
            /\ taskStatus' = [taskStatus EXCEPT ![t] = "done"]
            /\ processorStatus' = [processorStatus EXCEPT ![p] = "free"]
            /\ taskProcessorMap' = [taskProcessorMap EXCEPT ![p] = "none"]
        /\ UNCHANGED << queue1, queue2, queue3, taskRemainingTime, clock, processorTimeLeft >>
 

UpdateClock ==
    /\ \E p \in Processors: processorStatus[p] = "busy"
    /\ \A p \in Processors, t \in Tasks : ((processorStatus[p] = "busy" /\ t = taskProcessorMap[p]) => (processorTimeLeft[p] > 0 /\ taskRemainingTime[t] > 0))
    /\ clock' = clock + 1
    /\ processorTimeLeft' = [p \in Processors |-> IF processorStatus[p] = "busy" THEN processorTimeLeft[p] - 1 ELSE processorTimeLeft[p]]
    /\ taskRemainingTime' = [t \in Tasks |-> 
                                IF \E p \in Processors: taskProcessorMap[p] = t /\ taskStatus[t] = "executing" 
                                THEN taskRemainingTime[t] - 1 
                                ELSE taskRemainingTime[t]]
    /\ UNCHANGED << queue1, queue2, queue3, taskStatus, processorStatus, taskProcessorMap >>
    

(* --next state relation
Describe how the system transitions from one state to another.
*)
Next ==
    \/ /\ \E t \in Tasks : taskStatus[t] /= "done"
       /\ (   ExecuteTask
            \/ RemoveTask
            \/ PreemptTask
            \/ UpdateClock )
    \/ /\ \A t \in Tasks : taskStatus[t] = "done"
       /\ UNCHANGED vars
       
\*State Constraint
Inv == clock < 10

(* --specification
The system should always start in the Init state and then make transitions based on the Next relation.
*)
Spec ==
    Init /\ [][Next]_vars /\ SF_vars(ExecuteTask) /\ SF_vars(PreemptTask) /\ SF_vars(RemoveTask) /\ SF_vars(UpdateClock)

\*safety properties
(* --
Define safety properties like no task is executed by two processors simultaneously.
*)
NoConcurrentExecution ==
    \A p1, p2 \in Processors : 
        \A t \in Tasks :
            (taskProcessorMap[p1] = t /\ taskProcessorMap[p2] = t) => p1 = p2
     
(* --safety properties
A safety property that ensures that no task is executed more than its burst time.
*)       
ExecutionWithinBurstTime == \A t \in Tasks: taskRemainingTime[t] >= 0
 
\*liveness properties
(* --
Define liveness properties like every task eventually gets executed.
*)
ExecuteAllTAsks ==
    \A t \in Tasks : <>(taskStatus[t] = "done")

EventuallyQueuesEmpty == <>[] (Len(queue1) = 0 /\ Len(queue2) = 0 /\ Len(queue3) = 0)

EventuallyProcessorsFree == <> (\A p \in Processors: processorStatus[p] = "free")

(* --
A liveness property that ensures that every task that is waiting in a queue eventually gets the CPU
*)
NoStarvation ==
        \A t \in Tasks: (taskStatus[t] = "waiting") => <>(taskStatus[t] = "executing")

(* --
A liveness property that ensures that every task that is executing by a processor eventually finishes its execution, which means that no task is executed indefinitely.
*)
Termination == 
        \A t \in Tasks: (taskStatus[t] = "executing") => <>(taskStatus[t] = "done")
        
(* --model checking
Specify the properties to be checked by the model checker.
*)
Properties ==
    /\ ExecuteAllTAsks
    /\ NoConcurrentExecution
    /\ EventuallyQueuesEmpty
    /\ EventuallyProcessorsFree
    /\ ExecutionWithinBurstTime
    /\ NoStarvation
    /\ Termination

    
=============================================================================
\* Modification History
\* Last modified Wed Dec 06 10:51:54 EST 2023 by sarthakd
\* Last modified Tue Dec 05 22:32:18 EST 2023 by simranmakhija
\* Created Wed Nov 29 02:44:25 EST 2023 by sarthakd