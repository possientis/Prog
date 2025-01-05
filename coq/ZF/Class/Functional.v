Require Import ZF.Binary.Functional.
Require Import ZF.Class.
Require Import ZF.Class.FromBinary.
Require Import ZF.Core.Dot.
Require Import ZF.Core.Equiv.
Require Import ZF.Set.
Require Import ZF.Set.OrdPair.

(* A class is said to be functional if its associated binary class is           *)
Definition Functional (F:Class) : Prop
  := Binary.Functional.Functional (toBinary F).

(* Using FunctionalCharac below with '<->' does not always work as expected.    *)
Proposition FunctionalCharac1 : forall (F:Class),
  Functional F -> (forall x y z, F :(x,y): -> F :(x,z): -> y = z).
Proof.
  intros F H1. apply H1.
Qed.

(* Using FunctionalCharac below with '<->' does not always work as expected.    *)
Proposition FunctionalCharac2 : forall (F:Class),
  (forall x y z, F :(x,y): -> F :(x,z): -> y = z) -> Functional F.
Proof.
  intros F H1.
  unfold Functional, Binary.Functional.Functional, toBinary. assumption.
Qed.

Proposition FunctionalCharac : forall (F:Class),
  Functional F <-> (forall x y z, F :(x,y): -> F :(x,z): -> y = z).
Proof.
  intros F. split.
  - apply FunctionalCharac1.
  - apply FunctionalCharac2.
Qed.

Proposition FunctionalEquivCompat : forall (F G:Class),
  F :~: G -> Functional F -> Functional G.
Proof.
  intros F G H1 H2. apply FunctionalCharac2.
  intros x y z H3 H4. remember (FunctionalCharac1 F H2) as H5 eqn:E. clear E H2.
  apply H5 with x; apply H1; assumption.
Qed.
