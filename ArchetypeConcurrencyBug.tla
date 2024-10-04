---- MODULE ArchetypeConcurrencyBug ----
(*******************)
(* A -1-> B        *)
(*        B -2-> C *)
(* A ---3------> C *)
(*******************)
EXTENDS Naturals, Sequences
VARIABLES queue_a, queue_b, queue_c, received_third, received_second, sent_messages
CONSTANT QLen
ASSUME (QLen \in Nat) /\ (QLen > 0)
----

Messages == {"First", "Second", "Third"}

Init == /\ queue_a = << >>
        /\ queue_b = << >>
        /\ queue_c = << >>
        /\ received_second = FALSE
        /\ received_third = FALSE
        /\ sent_messages = FALSE

TypeInvariant == /\ queue_a \in Seq(Messages)
                 /\ queue_b \in Seq(Messages)
                 /\ queue_c \in Seq(Messages)

----

ReceiveQueueC == LET new == Head(queue_c)
                        IN  /\ (queue_c # << >>)
                            /\ received_third = FALSE
                            /\ queue_c' = Tail(queue_c)
                            /\ new = "Third"
                            /\ received_third' = TRUE
                            /\ UNCHANGED <<queue_b, queue_a, received_second, sent_messages>>

ReceiveQueueB == LET new == Head(queue_b)
                        IN  /\ (queue_b # << >>)
                            /\ received_third = FALSE
                            /\ queue_b' = Tail(queue_b)
                            /\ new = "Second"
                            /\ received_second' = TRUE
                            /\ UNCHANGED <<queue_c, queue_a, received_third, sent_messages>>

ReceiveQueueA == LET new == Head(queue_a)
                        IN  /\ (queue_a # << >>)
                            /\ new = "First"
                            /\ queue_a' = Tail(queue_a)
                            /\ Len(queue_b) < QLen
                            /\ queue_b' = Append(queue_b, "Second")
                            /\ UNCHANGED <<queue_c, received_second, received_third, sent_messages>>

SendMessages == /\ queue_a' = Append(queue_a, "First")
                /\ Len(queue_a) < QLen
                /\ queue_c' = Append(queue_c, "Third")
                /\ Len(queue_c) < QLen
                /\ sent_messages = FALSE
                /\ sent_messages' = TRUE
                /\ UNCHANGED <<queue_b, received_second, received_third>>

Done == /\ received_third = TRUE
        /\ received_second = TRUE
        /\ UNCHANGED <<queue_a, queue_b, queue_c, received_third, received_second, sent_messages>>

Next == \/ SendMessages
        \/ ReceiveQueueA
        \/ ReceiveQueueB
        \/ ReceiveQueueC
        \/ Done

Spec ==
    Init /\ [][Next]_<<queue_a, queue_b, queue_c, received_third, received_second, sent_messages>>
----
THEOREM Spec => []TypeInvariant
====