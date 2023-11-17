---------------------- MODULE RoundRobin ----------------------
EXTENDS Integers, Sequences

CONSTANTS Processors

Tasks == {"t1","t2"}

VARIABLES readyQueue, taskStatus, clock, processorStatus, taskProcessorMap

vars  == <<readyQueue, taskStatus, clock, processorStatus, taskProcessorMap>>

TypeOK ==
        /\ taskStatus \in {"waiting", "executing", "done"}
        /\ processorStatus \in {"busy", "free" }

(* -- Convert a set to a sequence *)
\*SetToSeq(S) ==
\*    LET SeqBuilder(s) == IF s = {} THEN << >>
\*                         ELSE LET elem == CHOOSE x \in s: TRUE
\*                              IN  << elem >> \o SeqBuilder(s \ {elem})
\*    IN  SeqBuilder(S)
\*
\*TasksSeq == SetToSeq(Tasks)         
    
(* --initial state definition
The readyQueue is initially empty, taskStatus is a mapping of each task to its state,
and the clock starts at 0.
*)
Init ==
    /\ readyQueue = <<"t1", "t2">>
    /\ taskStatus = [t \in Tasks |-> "waiting"]
    /\ processorStatus = [ p \in Processors |-> "free"]
    /\ taskProcessorMap = [ p \in Processors |-> {}]
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
        /\ readyQueue' = Tail(readyQueue)
    /\ UNCHANGED clock   
    
   

 RemoveTask ==
    /\ \E t \in Tasks, p \in Processors : 
        /\ taskStatus[t] = "executing"
        /\ taskProcessorMap[p] = t
        /\ taskStatus' = [taskStatus EXCEPT ![t] = "done"]
        /\ processorStatus' = [processorStatus EXCEPT ![p] = "free"]
        /\ taskProcessorMap' = [taskProcessorMap EXCEPT ![p] = {}]
    /\ UNCHANGED << readyQueue, clock >>

(* --next state relation
Describe how the system transitions from one state to another.
*)
Next ==
    \/ ExecuteTask    
    \/ clock' = clock + 1

(* --specification
The system should always start in the Init state and then make transitions based on the Next relation.
*)
Spec ==
    Init /\ [][Next]_vars

(* --safety properties
Define safety properties like no task is executed by two processors simultaneously.
*)
\*NoConcurrentExecution ==
\*    /\ \A p1, p2 \in Processors:
\*         p1 /= p2 => (taskStatus[p1] /= "busy" \/ taskStatus[p2] /= "busy")

(* --liveness properties
Define liveness properties like every task eventually gets executed.
*)
FairExecution ==
    \A t \in Tasks : <>(taskStatus[t] = "done")

(* --model checking
Specify the properties to be checked by the model checker.
*)
Properties ==
    /\ FairExecution

=============================================================================
