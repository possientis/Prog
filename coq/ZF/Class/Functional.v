Require Import ZF.Binary.Functional.
Require Import ZF.Class.
Require Import ZF.Class.Compose.
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

Proposition ComposeIsFunctional : forall (F G:Class),
  Functional F -> Functional G -> Functional (G :.: F).
Proof.
  intros F G Hf Hg.
  remember (FunctionalCharac1 F Hf) as Gf eqn:E. clear E Hf.
  remember (FunctionalCharac1 G Hg) as Gg eqn:E. clear E Hg.
  apply FunctionalCharac2. intros x z1 z2 H1 H2.
  apply ComposeCharac2 in H1. destruct H1 as [y1 [H1 G1]].
  apply ComposeCharac2 in H2. destruct H2 as [y2 [H2 G2]].
  assert (y1 = y2) as H3. { apply Gf with x; assumption. }
  subst. apply Gg with y2; assumption.
Qed.

