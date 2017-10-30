Require Import list.
Require Import nat.
Require Import bool.


Theorem silly1 : forall (n m o p:nat),
    n = m -> [n,o] = [n,p] -> [n,o] = [m,p].
Proof.
    intros n m o p H1 H2. rewrite <- H1. exact H2.
Qed.


Theorem silly2 : forall (n m o p:nat),
    n = m -> (forall (q r:nat), q = r -> [q,o] = [r,p]) -> [n,o] = [m,p].
Proof.
    intros n m o p H1 H2. apply H2. exact H1.
Qed.


Theorem silly_ex : (forall n:nat, evenb n = true -> oddb (S n) = true) ->
    evenb 3 = true -> oddb 4 = true.
Proof. intros H1 H2. apply H1. exact H2. Qed.


