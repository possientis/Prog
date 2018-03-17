Require Import list.
Require Import In.

Theorem In10 : In 10 [1,2,3,4,5,6,7,8,9,10,11,12].
Proof. repeat (try (left; reflexivity); right). Qed.


Tactic Notation "simpl_and_try" tactic(c) :=
    simpl;
    try c.


    

