Require Import ZF.Axiom.Classic.
Require Import ZF.Class.
Require Import ZF.Set.
Require Import ZF.Set.OrdPair.

(* Local property of being functional at point a.                               *)
Definition FunctionalAt (F:Class) (a:U) : Prop :=
  forall y z, F :(a,y): -> F :(a,z): -> y = z.

(* The property of being functional at a is compatible with equivalence.        *)
Proposition FunctionalAtEquivCompat : forall (F G:Class) (a:U),
  F :~: G -> FunctionalAt F a -> FunctionalAt G a.
Proof.
  intros F G a H1 H2 y z H3 H4. apply H2; apply H1; assumption.
Qed.

Proposition NotFunctionalAt : forall (F:Class) (a:U),
  ~ FunctionalAt F a <-> exists y z, ~ y = z /\ F :(a,y): /\ F :(a,z):.
Proof.
  intros F a. split; intros H1.
  - apply NotForAll in H1. destruct H1 as [y H1].
    apply NotForAll in H1. destruct H1 as [z H1].
    exists y. exists z. split.
    + intros H2. subst. apply H1. intros _ _. reflexivity.
    + split.
      * apply DoubleNegation. intros H2. apply H1. intros H3. contradiction.
      * apply DoubleNegation. intros H2. apply H1. intros _ H3. contradiction.
  - destruct H1 as [y [z [H1 [H2 H3]]]]. intros H4. apply H1, H4; assumption.
Qed.
