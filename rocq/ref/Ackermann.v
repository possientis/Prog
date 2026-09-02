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


Lemma ackEqual : forall (n m:nat), Ack n m = Ackermann n m.
Proof.
    induction n as [|n IH].
    - intros m. rewrite Ack0. reflexivity.
    - induction m as [|m IH'].
        + simpl. rewrite Ack1. apply IH.
        + rewrite Ack2. simpl. rewrite IH'. apply IH.
Qed.

Hint Rewrite Ack0 Ack1 Ack2 : base0.

Lemma ResAck0 : Ack 3 2 = 29.
Proof.
    autorewrite with base0 using try reflexivity.
Qed.
