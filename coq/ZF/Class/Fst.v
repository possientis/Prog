Require Import ZF.Class.
Require Import ZF.Class.Functional.
Require Import ZF.Set.
Require Import ZF.Set.OrdPair.

(* Fst is the class of ordered pairs of the form ((y,z),y).                     *)
Definition Fst : Class := fun x =>
  exists y, exists z, x = :(:(y,z):,y):.

Proposition FstCharac2 : forall (x x':U),
  Fst :(x,x'): <-> exists y, exists z, x = :(y,z): /\ x' = y.
Proof.
  intros x x'. split; intros H1.
  - unfold Fst in H1. destruct H1 as [y [z H1]]. apply OrdPairEqual in H1.
    exists y. exists z. assumption.
  - destruct H1 as [y [z [H1 H2]]]. unfold Fst. exists y. exists z.
    rewrite H1, H2. reflexivity.
Qed.

Proposition FstIsFunctional : Functional Fst.
Proof.
  apply FunctionalCharac2. intros x x1 x2 H1 H2.
  apply FstCharac2 in H1. apply FstCharac2 in H2.
  destruct H1 as [y1 [z1 [H1 G1]]]. destruct H2 as [y2 [z2 [H2 G2]]].
  subst. apply OrdPairEqual in H2. destruct H2 as [H1 H2]. subst. reflexivity.
Qed.
