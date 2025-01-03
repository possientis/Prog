Require Import ZF.Binary.
Require Import ZF.Binary.Functional.
Require Import ZF.Core.Equiv.
Require Import ZF.Set.

(* Local property of being functional at point a.                               *)
Definition FunctionalAt (F:Binary) (a:U) : Prop :=
  forall y, forall z, F a y -> F a z -> y = z.

(* A functional binary class is functional at all points.                       *)
Proposition FunctionalIsFunctionalAt : forall (F:Binary) (a:U),
  Functional F -> FunctionalAt F a.
Proof.
  intros F a H1. unfold FunctionalAt. apply H1.
Qed.

(* The property of being functional at a is compatible with equivalence.        *)
Proposition FunctionalAtEquivCompat : forall (F G:Binary) (a:U),
  F :~: G -> FunctionalAt F a -> FunctionalAt G a.
Proof.
  intros F G a H1. unfold FunctionalAt. intros H2 y z H3 H4.
  apply H2; apply H1; assumption.
Qed.
