Require Import ZF.Binary.Functional.
Require Import ZF.Class.
Require Import ZF.Class.Compose.
Require Import ZF.Class.FromBinary.
Require Import ZF.Core.Dot.
Require Import ZF.Core.Equiv.
Require Import ZF.Set.
Require Import ZF.Set.OrdPair.

(* A class is said to be functional if its associated binary class is           *)
Definition Functional (P:Class) : Prop
  := Binary.Functional.Functional (toBinary P).

(* Using FunctionalCharac below with '<->' does not always work as expected.    *)
Proposition FunctionalCharac1 : forall (P:Class),
  Functional P -> (forall x y z, P :(x,y): -> P :(x,z): -> y = z).
Proof.
  intros P H1. apply H1.
Qed.

(* Using FunctionalCharac below with '<->' does not always work as expected.    *)
Proposition FunctionalCharac2 : forall (P:Class),
  (forall x y z, P :(x,y): -> P :(x,z): -> y = z) -> Functional P.
Proof.
  intros P H1.
  unfold Functional, Binary.Functional.Functional, toBinary. assumption.
Qed.

Proposition FunctionalCharac : forall (P:Class),
  Functional P <-> (forall x y z, P :(x,y): -> P :(x,z): -> y = z).
Proof.
  intros P. split.
  - apply FunctionalCharac1.
  - apply FunctionalCharac2.
Qed.

Proposition FunctionalEqualCompat : forall (P Q:Class),
  P :~: Q -> Functional P -> Functional Q.
Proof.
  intros P Q H1 H2. apply FunctionalCharac2.
  intros x y z H3 H4. remember (FunctionalCharac1 P H2) as H5 eqn:E. clear E H2.
  apply H5 with x; apply H1; assumption.
Qed.

Proposition ComposeIsFunctional : forall (P Q:Class),
  Functional P -> Functional Q -> Functional (Q :.: P).
Proof.
  intros P Q Hp Hq.
  remember (FunctionalCharac1 P Hp) as Gp eqn:E. clear E Hp.
  remember (FunctionalCharac1 Q Hq) as Gq eqn:E. clear E Hq.
  apply FunctionalCharac2. intros x z1 z2 H1 H2.
  apply ComposeCharac2 in H1. destruct H1 as [y1 [H1 G1]].
  apply ComposeCharac2 in H2. destruct H2 as [y2 [H2 G2]].
  assert (y1 = y2) as H3. { apply Gp with x; assumption. }
  subst. apply Gq with y2; assumption.
Qed.

