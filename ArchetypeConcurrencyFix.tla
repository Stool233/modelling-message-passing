---- MODULE ArchetypeConcurrencyFix ----
(*******************)
(* A -1-> B        *)
(*        B -2-> C *)
(*        B -3-> C *)
(*******************)
EXTENDS Naturals, Sequences
VARIABLES queue_a, queue_b, received_third, received_second, sent_messages
CONSTANT QLen
ASSUME (QLen \in Nat) /\ (QLen > 1)
----

Messages == {"First", "Second", "Third"}

Init == /\ queue_a = << >>
        /\ queue_b = << >>
        /\ received_second = FALSE
        /\ received_third = FALSE
        /\ sent_messages = FALSE

TypeInvariant == /\ queue_a \in Seq(Messages)
                 /\ queue_b \in Seq(Messages)
----

ReceiveThird == LET new == Head(queue_b)
                        IN  /\ (queue_b # << >>)
                            /\ received_third = FALSE
                            /\ queue_b' = Tail(queue_b)
                            /\ new = "Third"
                            /\ received_third' = TRUE
                            /\ UNCHANGED <<queue_a, received_second, sent_messages>>

ReceiveSecond == LET new == Head(queue_b)
                        IN  /\ (queue_b # << >>)
                            /\ received_third = FALSE
                            /\ queue_b' = Tail(queue_b)
                            /\ new = "Second"
                            /\ received_second' = TRUE
                            /\ UNCHANGED <<queue_a, received_third, sent_messages>>

ReceiveFirst == LET new == Head(queue_a)
                        IN  /\ (queue_a # << >>)
                            /\ new = "First"
                            /\ queue_a' = Tail(queue_a)
                            /\ Len(queue_b) < QLen
                            /\ queue_b' = <<"Second", "Third">>
                            /\ UNCHANGED <<received_second, received_third, sent_messages>>

SendMessages == /\ queue_a' = Append(queue_a, "First")
                /\ Len(queue_a) < QLen
                /\ sent_messages = FALSE
                /\ sent_messages' = TRUE
                /\ UNCHANGED <<queue_b, received_second, received_third>>

DONE == /\ received_third = TRUE
        /\ received_second = TRUE
        /\ UNCHANGED <<queue_a, queue_b, received_third, received_second, sent_messages>>

Next == \/ SendMessages
        \/ ReceiveFirst
        \/ ReceiveSecond
        \/ ReceiveThird
        \/ DONE

Spec ==
    Init /\ [][Next]_<<queue_a, queue_b, received_third, received_second, sent_messages>>
----
THEOREM Spec => []TypeInvariant
====