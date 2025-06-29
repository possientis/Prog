Require Import ZF.Axiom.Classic.
Require Import ZF.Class.Equiv.
Require Import ZF.Class.Relation.FunctionalAt.
Require Import ZF.Set.Core.
Require Import ZF.Set.OrdPair.

(* Local property of a set a being functional at the point b.                   *)
Definition FunctionalAt (a b:U) : Prop :=
  forall y z, :(b,y): :< a -> :(b,z): :< a -> y = z.

Proposition ToClass : forall (a b:U),
  FunctionalAt a b <-> Class.Relation.FunctionalAt.FunctionalAt (toClass a) b.
Proof.
  intros a b. split; intros H1; assumption.
Qed.

Proposition WhenNot : forall (a b:U),
  ~ FunctionalAt a b <-> exists y z, y <> z /\ :(b,y): :< a /\ :(b,z): :< a.
Proof.
  intros a b. split; intros H1.
  - apply NotForAll in H1. destruct H1 as [y H1].
    apply NotForAll in H1. destruct H1 as [z H1].
    exists y. exists z. split.
    + intros H2. subst. apply H1. intros _ _. reflexivity.
    + split.
      * apply DoubleNegation. intros H2. apply H1. intros H3. contradiction.
      * apply DoubleNegation. intros H2. apply H1. intros _ H3. contradiction.
  - destruct H1 as [y [z [H1 [H2 H3]]]]. intros H4. apply H1, H4; assumption.
Qed.
