Require Import ZF.Binary.Compose.
Require Import ZF.Class.
Require Import ZF.Class.Bijection.
Require Import ZF.Class.Converse.
Require Import ZF.Class.Domain.
Require Import ZF.Class.FromBinary.
Require Import ZF.Class.Function.
Require Import ZF.Class.Functional.
Require Import ZF.Class.FunctionOn.
Require Import ZF.Class.Incl.
Require Import ZF.Class.OneToOne.
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

(* The composition of two functional classes is functional.                     *)
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

(* The composition of two functional classes is a function class.               *)
Proposition ComposeIsFunction : forall (F G:Class),
  Functional F -> Functional G -> Function (G :.: F).
Proof.
  intros F G Hf Hg. split.
  - apply ComposeIsRelation.
  - apply ComposeIsFunctional; assumption.
Qed.

(* The composition of two function classes is a function class.                 *)
Proposition ComposeIsFunction2 : forall (F G:Class),
  Function F -> Function G -> Function (G :.: F).
Proof.
  intros F G [_ Hf] [_ Hg]. apply ComposeIsFunction; assumption.
Qed.

(* The converse of the composition is (almost) the composition of the converse. *)
Proposition ComposeConverse : forall (P Q:Class),
  converse (Q :.: P) :~: converse P :.: converse Q.
Proof.
  intros P Q u. split; intros H1.
  - apply ConverseCharac in H1. destruct H1 as [x [z [H1 H2]]].
    apply ComposeCharac2 in H2. destruct H2 as [y [H2 H3]].
    apply ComposeCharac. exists z. exists y. exists x. split.
    + assumption.
    + split; apply ConverseCharac2; assumption.
  - apply ComposeCharac in H1. destruct H1 as [z [y [x [H1 [H2 H3]]]]].
    apply (proj1 (ConverseCharac2 _ _ _)) in H2.
    apply (proj1 (ConverseCharac2 _ _ _)) in H3.
    apply ConverseCharac. exists x. exists z. split.
    + assumption.
    + apply ComposeCharac2. exists y. split; assumption.
Qed.

(* The composition of two one-to-one classes is one-to-one.                     *)
Proposition ComposeIsOneToOne : forall (P Q:Class),
  OneToOne P -> OneToOne Q -> OneToOne (Q :.: P).
Proof.
  intros P Q [Hp Gp] [Hq Gq]. split.
  - apply ComposeIsFunctional; assumption.
  - apply FunctionalEquivCompat with (converse P :.: converse Q).
    + apply ClassEquivSym, ComposeConverse.
    + apply ComposeIsFunctional; assumption.
Qed.

(* The composition of two one-to-one classes is a bijection class.              *)
Proposition ComposeIsBijection : forall (F G:Class),
  OneToOne F -> OneToOne G -> Bijection (G :.: F).
Proof.
  intros F G Hf Hg. split.
  - apply ComposeIsRelation.
  - apply ComposeIsOneToOne; assumption.
Qed.

(* The composition of two bijection classes is a bijection class.               *)
Proposition ComposeIsBijection2 : forall (F G:Class),
  Bijection F -> Bijection G -> Bijection (G :.: F).
Proof.
  intros F G [_ Hf] [_ Hg]. apply ComposeIsBijection; assumption.
Qed.

(* The domain of the composition is a subclass of the first domain.             *)
Proposition ComposeDomainIsSmaller : forall (F G:Class),
  domain (G :.: F) :<=: domain F.
Proof.
  intros F G x H1. apply (proj1 (DomainCharac _ _)) in H1.
  destruct H1 as [z H1]. apply ComposeCharac2 in H1. destruct H1 as [y [H1 H2]].
  apply DomainCharac. exists y. assumption.
Qed.

(* The domain of the composition is the same as the first domain if range ok.   *)
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

(* If first class is functional, same domains conversely implies range is ok.   *)
Proposition ComposeDomainIsSame2 : forall (F G:Class),
  Functional F -> range F :<=: domain G <-> domain (G :.: F) :~: domain F.
Proof.
  intros F G H1. split.
  - apply ComposeDomainIsSame.
  - intros H2 y H3. apply (proj1 (RangeCharac _ _)) in H3. destruct H3 as [x H3].
    assert (domain (G :.: F) x) as H4. { apply H2, DomainCharac. exists y. assumption. }
    apply (proj1 (DomainCharac _ _)) in H4. destruct H4 as [z H4].
    apply ComposeCharac2 in H4. destruct H4 as [y' [H4 H5]].
    assert (y' = y) as H6. { apply FunctionalCharac1 with F x; assumption. }
    subst. apply DomainCharac. exists z. assumption.
Qed.

(* Composition is a function class defined on A if fist class is and range ok.  *)
Proposition ComposeIsFunctionOn : forall (F A G B:Class),
  FunctionOn F A ->
  FunctionOn G B ->
  range F :<=: B ->
  FunctionOn (G :.: F) A.
Proof.
  intros F A G B [H1 H2] [H3 H4] H5. split.
  - apply ComposeIsFunction2; assumption.
  - apply ClassEquivTran with (domain F). 2: assumption.
    apply ComposeDomainIsSame. apply InclEquivCompatR with B. 2: assumption.
    apply ClassEquivSym. assumption.
Qed.


