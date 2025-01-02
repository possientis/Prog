Require Import ZF.Binary.FunctionalAt.
Require Import ZF.Class.
Require Import ZF.Class.FromBinary.
Require Import ZF.Class.Functional.
Require Import ZF.Core.Equiv.
Require Import ZF.Set.
Require Import ZF.Set.OrdPair.

(* Local property of being functional at point a.                               *)
Definition FunctionalAt (F:Class) (a:U) : Prop
  := Binary.FunctionalAt.FunctionalAt (toBinary F) a.

(* Using FunctionalAtCharac below with '<->' does not always work as expected.  *)
Proposition FunctionalAtCharac1 : forall (F:Class) (a:U),
  FunctionalAt F a -> (forall y z, F:(a,y): -> F:(a,z): -> y = z).
Proof.
  intros F a H1. apply H1.
Qed.

(* Using FunctionalAtCharac below with '<->' does not always work as expected.  *)
Proposition FunctionalAtCharac2 : forall (F:Class) (a:U),
  (forall y z, F:(a,y): -> F:(a,z): -> y = z) -> FunctionalAt F a.
Proof.
  intros F a H1.
  unfold FunctionalAt, Binary.FunctionalAt.FunctionalAt, toBinary. assumption.
Qed.

Proposition FunctionalAtCharac : forall (F:Class) (a:U),
  FunctionalAt F a <-> forall y z, F :(a,y): -> F :(a,z): -> y = z.
Proof.
  intros F a. split.
  - apply FunctionalAtCharac1.
  - apply FunctionalAtCharac2.
Qed.

(* A functional class is functional at all points.                              *)
Proposition FunctionalIsFunctionalAt : forall (F:Class) (a:U),
  Functional F -> FunctionalAt F a.
Proof.
  intros F a H1. apply FunctionalAtCharac, H1.
Qed.

(* The property of being functional at a is compatible with equivalence.        *)
Proposition FunctionalAtEquivCompat : forall (F G:Class) (a:U),
  F :~: G -> FunctionalAt F a -> FunctionalAt G a.
Proof.
  intros F G a H1 H2.
  remember (FunctionalAtCharac1 F a H2) as H3 eqn:E. clear E H2.
  apply FunctionalAtCharac2. intros y z H4 H5. apply H3; apply H1; assumption.
Qed.
