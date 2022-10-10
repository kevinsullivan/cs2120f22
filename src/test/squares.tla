---- MODULE squares  ----
EXTENDS TLC, Integers

(*--algorithm squares
variables
    x \in 1..11;

begin
    assert x ^ 2 <= 100;
end algorithm; *)
\* BEGIN TRANSLATION (chksum(pcal) = "ba67d89f" /\ chksum(tla) = "cea41459")
VARIABLES x, pc

vars == << x, pc >>

Init == (* Global variables *)
        /\ x \in 1..11
        /\ pc = "Lbl_1"

Lbl_1 == /\ pc = "Lbl_1"
         /\ Assert(x ^ 2 <= 100, "Failure of assertion at line 9, column 5.")
         /\ pc' = "Done"
         /\ x' = x

(* Allow infinite stuttering to prevent deadlock on termination. *)
Terminating == pc = "Done" /\ UNCHANGED vars

Next == Lbl_1
           \/ Terminating

Spec == Init /\ [][Next]_vars

Termination == <>(pc = "Done")

\* END TRANSLATION 
====
