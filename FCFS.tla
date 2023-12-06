------------------------------ MODULE Untitled ------------------------------

EXTENDS Integers, Sequences

Processors == {"p1", "p2"}
Tasks == {"t1", "t2", "t3"}
BurstTimes == [t1 |-> 8, t2 |-> 11, t3 |-> 2]

VARIABLES readyQueue, taskStatus, clock, processorStatus, taskProcessorMap, taskRemainingTime

vars == <<readyQueue, taskStatus, clock, processorStatus, taskProcessorMap, taskRemainingTime>>

TypeOK ==
    /\ taskStatus \in {"waiting", "executing", "done"}
    /\ processorStatus \in {"busy", "free"}

Init ==
    /\ readyQueue = <<"t1", "t2", "t3">>
    /\ taskStatus = [t \in Tasks |-> "waiting"]
    /\ processorStatus = [p \in Processors |-> "free"]
    /\ taskProcessorMap = [p \in Processors |-> "none"]
    /\ taskRemainingTime = [t \in Tasks |-> BurstTimes[t]]
    /\ clock = 0

ExecuteTask ==
    /\ Len(readyQueue) > 0
    /\ taskStatus[Head(readyQueue)] = "waiting"
    /\ \E p \in Processors :
        /\ processorStatus[p] = "free"
        /\ taskProcessorMap' = [taskProcessorMap EXCEPT ![p] = Head(readyQueue)]
        /\ processorStatus' = [processorStatus EXCEPT ![p] = "busy"]
        /\ taskStatus' = [taskStatus EXCEPT ![Head(readyQueue)] = "executing"]
        /\ readyQueue' = Tail(readyQueue)
    /\ UNCHANGED << clock, taskRemainingTime >>

RemoveTask ==
    /\ \E t \in Tasks, p \in Processors :
        /\ taskStatus[t] = "executing"
        /\ taskProcessorMap[p] = t
        /\ taskRemainingTime[t] = 0
        /\ taskStatus' = [taskStatus EXCEPT ![t] = "done"]
        /\ processorStatus' = [processorStatus EXCEPT ![p] = "free"]
        /\ taskProcessorMap' = [taskProcessorMap EXCEPT ![p] = "none"]
    /\ UNCHANGED << readyQueue, clock, taskRemainingTime >>

UpdateClock ==
    /\ \E p \in Processors: processorStatus[p] = "busy"
    /\ \A p \in Processors, t \in Tasks : ((processorStatus[p] = "busy" /\ t = taskProcessorMap[p]) => (taskRemainingTime[t] > 0))
    /\ clock' = clock + 1
    /\ taskRemainingTime' = [t \in Tasks |-> 
                                IF \E p \in Processors: taskProcessorMap[p] = t /\ taskStatus[t] = "executing"
                                THEN taskRemainingTime[t] - 1
                                ELSE taskRemainingTime[t]]
    /\ UNCHANGED << readyQueue, taskStatus, processorStatus, taskProcessorMap >>

Next ==
    \/ /\ \E t \in Tasks : taskStatus[t] /= "done"
       /\ (   ExecuteTask
            \/ RemoveTask
            \/ UpdateClock )
    \/ /\ \A t \in Tasks : taskStatus[t] = "done"
       /\ UNCHANGED vars

Inv == clock < 30

Spec ==
    Init /\ [][Next]_vars /\ SF_vars(ExecuteTask) /\ SF_vars(RemoveTask) /\ SF_vars(UpdateClock)
    
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

Properties ==
    /\ AllTasksDone
    /\ NoConcurrentExecution
=============================================================================
\* Modification History
\* Last modified Wed Dec 06 15:33:46 EST 2023 by sarthakd
\* Created Wed Dec 06 15:32:53 EST 2023 by sarthakd
