Require Import Coq.Arith.Mult.

Definition divides (n m:nat) : Prop := exists (k:nat), k * n = m.

Definition prime (p:nat) : Prop :=
    (p <> 1) /\ forall (n:nat), divides n p -> (n = 1) \/ (n = p).

Lemma DIVIDES_0 : forall (n:nat), divides n 0.
Proof. intros n. exists 0. reflexivity. Qed.

Lemma DIVIDES_ZERO : forall (n:nat), divides 0 n <-> n = 0.
Proof.
    intros. split; intros H.
    - destruct H as [k H]. 
      rewrite mult_comm in H. simpl in H. symmetry. assumption.
    - rewrite H. exists 0. reflexivity.
Qed.
