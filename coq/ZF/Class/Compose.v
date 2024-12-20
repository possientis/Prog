Require Import ZF.Binary.Compose.
Require Import ZF.Class.
Require Import ZF.Class.Binary.
Require Import ZF.Class.Function.
Require Import ZF.Class.Functional.
Require Import ZF.Class.Relation.
Require Import ZF.Core.Dot.
Require Import ZF.Set.
Require Import ZF.Set.OrdPair.

(* Composition of two classes.                                                  *)
Definition compose (Q P:Class) : Class
  := fromBinary (Binary.Compose.compose (toBinary Q) (toBinary P)).

(* Notation "Q :.: P" := (compose Q P)                                          *)
Global Instance ClassDot : Dot Class := { dot := compose }.

Proposition ComposeCharac : forall (P Q:Class) (u:U),
  (Q :.: P) u <-> exists x y z, u = :(x,z): /\ P :(x,y): /\ Q :(y,z):.
Proof.
  intros P Q. split; intros H1.
  - unfold dot, ClassDot, compose, Binary.Compose.compose, fromBinary, toBinary in H1.
    destruct H1 as [x [z [H1 [y [H2 H3]]]]].
    exists x. exists y. exists z. split.
    + assumption.
    + split; assumption.
  - unfold dot, ClassDot, compose, Binary.Compose.compose, fromBinary, toBinary.
    destruct H1 as [x [y [z [H1 [H2 H3]]]]]. exists x. exists z. split.
    + assumption.
    + exists y. split; assumption.
Qed.

Proposition ComposeCharac2 : forall (P Q:Class) (x z:U),
  (Q :.: P) :(x,z): <-> exists y, P :(x,y): /\ Q :(y,z):.
Proof.
  intros P Q x z. split; intros H1.
  - apply ComposeCharac in H1. destruct H1 as [x' [y [z' [H1 [H2 H3]]]]].
    apply OrdPairEqual in H1. destruct H1 as [H1 G1]. subst. exists y.
    split; assumption.
  - destruct H1 as [y [H1 H2]]. apply ComposeCharac.
    exists x. exists y. exists z. split.
    + reflexivity.
    + split; assumption.
Qed.

(* The composition of two classes is a relation.                                *)
Proposition ComposeIsRelation : forall (P Q:Class), Relation (P :.: Q).
Proof.
  intros P Q u H1. apply ComposeCharac in H1.
  destruct H1 as [x [y [z [H1 [H2 H3]]]]]. exists x. exists z. assumption.
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

Proposition ComposeIsFunction : forall (P Q:Class),
  Functional P -> Functional Q -> Function (Q :.: P).
Proof.
  intros P Q Hp Hq. split.
  - apply ComposeIsRelation.
  - apply ComposeIsFunctional; assumption.
Qed.
