Require Import Coq.Arith.Mult.
Require Import Coq.Arith.Plus.

Definition divides (n m:nat) : Prop := exists (k:nat), k * n = m.

Notation "n | m" := (divides n m) (at level 50).

Definition prime (p:nat) : Prop :=
    (p <> 1) /\ forall (n:nat), n | p -> (n = 1) \/ (n = p).

Lemma div_n_0 : forall (n:nat), n | 0.
Proof. intros n. exists 0. reflexivity. Qed.

Lemma div_0_n : forall (n:nat), 0 | n <-> n = 0.
Proof.
    intros. split; intros H.
    - destruct H as [k H]. 
      rewrite mult_comm in H. simpl in H. symmetry. assumption.
    - rewrite H. exists 0. reflexivity.
Qed.

Lemma div_n_1 : forall (n:nat), n | 1 <-> n = 1.
Proof.
    intros n. split.
    - intros [k H]. destruct n as [|n].
        + simpl in H. rewrite <- mult_n_O in H. inversion H.
        + destruct n as [|n].
            { reflexivity. }
            { destruct k as [|k].
                { simpl in H. inversion H. }
                { simpl in H. inversion H. }
            }
    - intros H. exists 1. rewrite H. reflexivity.
Qed.

