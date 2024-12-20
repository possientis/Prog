Require Import ZF.Binary.Functional.
Require Import ZF.Class.
Require Import ZF.Class.Binary.
Require Import ZF.Class.Compose.
Require Import ZF.Core.Dot.
Require Import ZF.Set.OrdPair.

(* A class is said to be functional if its associated binary class is           *)
Definition Functional (P:Class) : Prop := Functional.Functional (toBinary P).

Proposition FunctionalCharac1 : forall (P:Class),
  Functional P -> (forall x y z, P :(x,y): -> P :(x,z): -> y = z).
Proof.
  intros P H1. apply H1.
Qed.

Proposition FunctionalCharac2 : forall (P:Class),
  (forall x y z, P :(x,y): -> P :(x,z): -> y = z) -> Functional P.
Proof.
  intros P H1.
  unfold Functional, Binary.Functional.Functional, toBinary. assumption.
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


