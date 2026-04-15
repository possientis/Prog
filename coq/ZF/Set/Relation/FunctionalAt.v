Require Import ZF.Axiom.Classic.
Require Import ZF.Class.Equiv.
Require Import ZF.Class.Relation.FunctionalAt.
Require Import ZF.Set.Core.
Require Import ZF.Set.OrdPair.

Module CRA := ZF.Class.Relation.FunctionalAt.

(* Local property of a set f being functional at the point a.                   *)
Definition FunctionalAt (f a:U) : Prop :=
  forall y z, :(a,y): :< f -> :(a,z): :< f -> y = z.

Proposition ToClass : forall (f a:U),
  FunctionalAt f a -> CRA.FunctionalAt (toClass f) a.
Proof.
  intros f a H1. assumption.
Qed.

Proposition FromClass : forall (f a:U),
  CRA.FunctionalAt (toClass f) a -> FunctionalAt f a.
Proof.
  intros f a H1. assumption.
Qed.

Proposition WhenNot : forall (f a:U),
  ~ FunctionalAt f a <-> exists y z, y <> z /\ :(a,y): :< f /\ :(a,z): :< f.
Proof.
  intros f a. split; intros H1.
  - apply NotForAll in H1. destruct H1 as [y H1].
    apply NotForAll in H1. destruct H1 as [z H1].
    exists y. exists z. split.
    + intros H2. subst. apply H1. intros _ _. reflexivity.
    + split.
      * apply DoubleNegation. intros H2. apply H1. intros H3. contradiction.
      * apply DoubleNegation. intros H2. apply H1. intros _ H3. contradiction.
  - destruct H1 as [y [z [H1 [H2 H3]]]]. intros H4. apply H1, H4; assumption.
Qed.
