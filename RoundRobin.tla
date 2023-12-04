---------------------- MODULE RoundRobin ----------------------
EXTENDS Integers, Sequences

\*CONSTANTS Processors, Tasks, TimeQuanta, BurstTimes

Processors == {"p1", "p2"}
Tasks == {"t1", "t2","t3"}
TimeQuanta == 2
BurstTimes== [t1 |-> 8, t2 |-> 11, t3|-> 2]

VARIABLES readyQueue, taskStatus, clock, processorStatus, taskProcessorMap, processorTimeLeft, taskRemainingTime

vars  == <<readyQueue, taskStatus, clock, processorStatus, taskProcessorMap, processorTimeLeft, taskRemainingTime>>

TypeOK ==
        /\ taskStatus \in {"waiting", "executing", "done"}
        /\ processorStatus \in {"busy", "free" }  
    
(* --initial state definition
The readyQueue is initially empty, taskStatus is a mapping of each task to its state,
and the clock starts at 0.
*)
Init ==
    /\ readyQueue = <<"t1","t2","t3">>
    /\ taskStatus = [t \in Tasks |-> "waiting"]
    /\ processorStatus = [ p \in Processors |-> "free"]
    /\ taskProcessorMap = [ p \in Processors |-> "none"]
    /\ processorTimeLeft = [ p \in Processors |-> 0]
    /\ taskRemainingTime = [ t \in Tasks |-> BurstTimes[t]]
    /\ clock = 0

(* --action definitions
Define actions for scheduling tasks, executing tasks, and updating the queue.
*)
    
ExecuteTask ==
    /\ Len(readyQueue) > 0
    /\ taskStatus[Head(readyQueue)] = "waiting"
    /\ \E p \in Processors : 
        /\ processorStatus[p] = "free"
        /\ taskProcessorMap' = [taskProcessorMap EXCEPT ![p] = Head(readyQueue)]
        /\ processorStatus' = [processorStatus EXCEPT ![p] = "busy"]
        /\ taskStatus' = [taskStatus EXCEPT ![Head(readyQueue)] = "executing"]
        /\ processorTimeLeft' = [processorTimeLeft EXCEPT ![p] = TimeQuanta]
        /\ readyQueue' = Tail(readyQueue)
    /\ UNCHANGED << clock, taskRemainingTime >>
    
PreemptTask ==
    /\ \E p \in Processors, t \in Tasks : 
        /\ taskProcessorMap[p] = t
        /\ processorTimeLeft[p] = 0
        /\ taskRemainingTime[t] > 0
        /\ taskStatus' = [taskStatus EXCEPT ![t] = "waiting"]
        /\ processorStatus' = [processorStatus EXCEPT ![p] = "free"]
        /\ taskProcessorMap' = [taskProcessorMap EXCEPT ![p] = "none"]
        /\ readyQueue' = Append(readyQueue, t)
    /\ UNCHANGED << clock, processorTimeLeft, taskRemainingTime >>

RemoveTask ==
    /\ \E t \in Tasks, p \in Processors : 
        /\ taskStatus[t] = "executing"
        /\ taskProcessorMap[p] = t
        /\ taskRemainingTime[t] = 0
        /\ taskStatus' = [taskStatus EXCEPT ![t] = "done"]
        /\ processorStatus' = [processorStatus EXCEPT ![p] = "free"]
        /\ taskProcessorMap' = [taskProcessorMap EXCEPT ![p] = "none"]
    /\ UNCHANGED << readyQueue, clock, processorTimeLeft, taskRemainingTime >>


UpdateClock ==
    /\ \E p \in Processors: processorStatus[p] = "busy"
    /\ \A p \in Processors, t \in Tasks : ((processorStatus[p] = "busy" /\ t = taskProcessorMap[p]) => (processorTimeLeft[p] > 0 /\ taskRemainingTime[t] > 0))
    /\ clock' = clock + 1
    /\ processorTimeLeft' = [p \in Processors |-> IF processorStatus[p] = "busy" THEN processorTimeLeft[p] - 1 ELSE processorTimeLeft[p]]
    /\ taskRemainingTime' = [t \in Tasks |-> 
                                IF \E p \in Processors: taskProcessorMap[p] = t /\ taskStatus[t] = "executing" 
                                THEN taskRemainingTime[t] - 1 
                                ELSE taskRemainingTime[t]]
    /\ UNCHANGED << readyQueue, taskStatus, processorStatus, taskProcessorMap >>
    

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
      
Inv == clock < 30

(* --specification
The system should always start in the Init state and then make transitions based on the Next relation.
*)
Spec ==
    Init /\ [][Next]_vars /\ SF_vars(ExecuteTask) /\ SF_vars(PreemptTask) /\ SF_vars(RemoveTask) /\ SF_vars(UpdateClock)


(* --safety properties
Define safety properties like no task is executed by two processors simultaneously.
*)
NoConcurrentExecution ==
    \A p1, p2 \in Processors : 
        \A t \in Tasks :
            (taskProcessorMap[p1] = t /\ taskProcessorMap[p2] = t) => p1 = p2

(* --liveness properties
Define liveness properties like every task eventually gets executed.
*)
AllTasksDone ==
    \A t \in Tasks : <>(taskStatus[t] = "done")

(* --model checking
Specify the properties to be checked by the model checker.
*)
Properties ==
    /\ AllTasksDone
    /\ NoConcurrentExecution

=============================================================================