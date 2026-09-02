Require Import nat.
Require Import bool.
Require Import induction.


Theorem S_inj : forall (n m:nat) (b:bool),
    eqb (S n) (S m) = b -> eqb n m = b.
Proof. intros n m b H. simpl in H. exact H. Qed.


Theorem silly3' : forall (n:nat),
    (eqb n 5 = true -> eqb (S (S n)) 7 = true) ->
    true = eqb n 5 ->
    true = eqb (S (S n)) 7.
Proof.
    intros n H1 H2. symmetry in H2. apply H1 in H2. 
    symmetry in H2. exact H2.
Qed.

Theorem plus_n_n_injective : forall (n m:nat),
    n + n = m + m -> n = m.
Proof.
    induction n as [|n H].
    - intros m H. destruct m as [|m].
        + reflexivity.
        + simpl in H. inversion H.
    - intros m H'. destruct m.
        + simpl in H'. inversion H'.
        + simpl in H'. inversion H' as [H1]. clear H'.
            rewrite (plus_comm n (S n)) in H1.
            rewrite (plus_comm m (S m)) in H1.
            simpl in H1. inversion H1 as [H']. clear H1.
            apply H in H'. rewrite H'. reflexivity.
Qed.


