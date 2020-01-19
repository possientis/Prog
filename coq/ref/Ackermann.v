Require Import Arith.

Variable Ack : nat -> nat -> nat.

Axiom Ack0 : forall (m:nat), Ack 0 m = S m.
Axiom Ack1 : forall (n:nat), Ack (S n) 0 = Ack n 1.
Axiom Ack2 : forall (n m:nat), Ack (S n) (S m) = Ack n (Ack (S n) m).

Fixpoint Ackermann (n:nat) : nat -> nat :=
    match n with 
    | 0     => fun m => S m
    | S n   => fix g (m:nat) :=
        match m with
        | 0     => Ackermann n 1
        | S m   => Ackermann n (g m)
        end
    end.
