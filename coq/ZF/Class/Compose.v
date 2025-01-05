Require Import ZF.Binary.Compose.
Require Import ZF.Class.
Require Import ZF.Class.Domain.
Require Import ZF.Class.FromBinary.
Require Import ZF.Class.Function.
Require Import ZF.Class.Functional.
Require Import ZF.Class.FunctionOn.
Require Import ZF.Class.Incl.
Require Import ZF.Class.Range.
Require Import ZF.Class.Rel.
Require Import ZF.Core.Dot.
Require Import ZF.Core.Equiv.
Require Import ZF.Core.Leq.
Require Import ZF.Set.
Require Import ZF.Set.OrdPair.

(* Composition of two classes.                                                  *)
Definition compose (G F:Class) : Class
  := fromBinary (Binary.Compose.compose (toBinary G) (toBinary F)).

(* Notation "G :.: F" := (compose G F)                                          *)
Global Instance ClassDot : Dot Class := { dot := compose }.

Proposition ComposeCharac : forall (F G:Class) (u:U),
  (G :.: F) u <-> exists x y z, u = :(x,z): /\ F :(x,y): /\ G :(y,z):.
Proof.
  intros F G. split; intros H1.
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

Proposition ComposeCharac2 : forall (F G:Class) (x z:U),
  (G :.: F) :(x,z): <-> exists y, F :(x,y): /\ G :(y,z):.
Proof.
  intros F G x z. split; intros H1.
  - apply ComposeCharac in H1. destruct H1 as [x' [y [z' [H1 [H2 H3]]]]].
    apply OrdPairEqual in H1. destruct H1 as [H1 G1]. subst. exists y.
    split; assumption.
  - destruct H1 as [y [H1 H2]]. apply ComposeCharac.
    exists x. exists y. exists z. split.
    + reflexivity.
    + split; assumption.
Qed.

(* The composition of two classes is a relation.                                *)
Proposition ComposeIsRelation : forall (F G:Class), Rel (G :.: F).
Proof.
  intros F G u H1. apply ComposeCharac in H1.
  destruct H1 as [x [y [z [H1 [H2 H3]]]]]. exists x. exists z. assumption.
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

Proposition ComposeIsFunction : forall (F G:Class),
  Functional F -> Functional G -> Function (G :.: F).
Proof.
  intros F G Hf Hg. split.
  - apply ComposeIsRelation.
  - apply ComposeIsFunctional; assumption.
Qed.

(* Weaker result but convenient                                                 *)
Proposition ComposeIsFunction2 : forall (F G:Class),
  Function F -> Function G -> Function (G :.: F).
Proof.
  intros F G [_ Hf] [_ Hg]. apply ComposeIsFunction; assumption.
Qed.

Proposition ComposeDomainIsSmaller : forall (F G:Class),
  domain (G :.: F) :<=: domain F.
Proof.
  intros F G x H1. apply (proj1 (DomainCharac _ _)) in H1.
  destruct H1 as [z H1]. apply ComposeCharac2 in H1. destruct H1 as [y [H1 H2]].
  apply DomainCharac. exists y. assumption.
Qed.

Proposition ComposeDomainIsSame : forall (F G:Class),
  range F :<=: domain G -> domain (G :.: F) :~: domain F.
Proof.
  intros F G H1. apply DoubleInclusion. split.
  - apply ComposeDomainIsSmaller.
  - intros x H2. apply (proj1 (DomainCharac _ _)) in H2. destruct H2 as [y H2].
    assert (domain G y) as H3. { apply H1. apply RangeCharac. exists x. assumption. }
    apply (proj1 (DomainCharac _ _)) in H3. destruct H3 as [z H3].
    apply DomainCharac. exists z. apply ComposeCharac2. exists y.
    split; assumption.
Qed.

Proposition ComposeIsFunctionOn : forall (F A G B:Class),
  FunctionOn F A ->
  FunctionOn G B ->
  range F :<=: B ->
  FunctionOn (G :.: F) A.
Proof.
  intros F A G B [H1 H2] [H3 H4] H5. split.
  -
Admitted.

