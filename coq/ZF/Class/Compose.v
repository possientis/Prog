Require Import ZF.Class.
Require Import ZF.Class.Converse.
Require Import ZF.Class.Domain.
Require Import ZF.Class.Functional.
Require Import ZF.Class.FunctionalAt.
Require Import ZF.Class.Image.
Require Import ZF.Class.Incl.
Require Import ZF.Class.Range.
Require Import ZF.Class.Relation.
Require Import ZF.Set.
Require Import ZF.Set.Eval.
Require Import ZF.Set.OrdPair.

Require Import ZF.Core.Dot.
Export ZF.Core.Dot.

(* Composition of two classes.                                                  *)
Definition compose (G F:Class) : Class := fun u =>
  exists x y z, u = :(x,z): /\ F :(x,y): /\ G :(y,z):.


(* Notation "G :.: F" := (compose G F)                                          *)
Global Instance ClassDot : Dot Class := { dot := compose }.

Proposition ComposeCharac2 : forall (F G:Class) (x z:U),
  (G :.: F) :(x,z): <-> exists y, F :(x,y): /\ G :(y,z):.
Proof.
  intros F G x z. split; intros H1.
  - destruct H1 as [x' [y [z' [H1 [H2 H3]]]]].
    apply OrdPairEqual in H1. destruct H1 as [H1 G1]. subst. exists y.
    split; assumption.
  - destruct H1 as [y [H1 H2]]. exists x. exists y. exists z. split.
    + reflexivity.
    + split; assumption.
Qed.

(* Composition is compatible with class equivalence.                            *)
Proposition ComposeEquivCompat : forall (F F' G G':Class),
  F :~: F' -> G :~: G' -> G :.: F :~: G' :.: F'.
Proof.
  intros F F' G G' H1 H2 u. split; intros H3;
  destruct H3 as [x [y [z [H3 [H4 H5]]]]]; subst;
  apply ComposeCharac2; exists y; split.
  - apply H1. assumption.
  - apply H2. assumption.
  - apply H1. assumption.
  - apply H2. assumption.
Qed.

(* Composition is left-compatible with class equivalence.                       *)
Proposition ComposeEquivCompatL : forall (F G G':Class),
  G :~: G' -> G :.: F :~: G' :.: F.
Proof.
  intros F G G' H1. apply ComposeEquivCompat.
  - apply Class.EquivRefl.
  - assumption.
Qed.

(* Composition is right-compatible with class equivalence.                      *)
Proposition ComposeEquivCompatR : forall (F F' G:Class),
  F :~: F' -> G :.: F :~: G :.: F'.
Proof.
  intros F F' G H1. apply ComposeEquivCompat.
  - assumption.
  - apply Class.EquivRefl.
Qed.

(* The composition of two classes is a relation.                                *)
Proposition ComposeIsRelation : forall (F G:Class), Relation (G :.: F).
Proof.
  intros F G u [x [y [z [H1 [H2 H3]]]]]. exists x. exists z. assumption.
Qed.

(* The composition of two functional classes is functional.                     *)
Proposition ComposeIsFunctional : forall (F G:Class),
  Functional F -> Functional G -> Functional (G :.: F).
Proof.
  intros F G H1 H2 x z1 z2 H3 H4.
  apply ComposeCharac2 in H3. destruct H3 as [y1 [H3 H5]].
  apply ComposeCharac2 in H4. destruct H4 as [y2 [H4 H6]].
  assert (y1 = y2) as H7. { apply H1 with x; assumption. }
  subst. apply H2 with y2; assumption.
Qed.

(* The converse of the composition is (almost) the composition of the converse. *)
Proposition ComposeConverse : forall (F G:Class),
  (G :.: F)^:-1: :~: F^:-1: :.: G^:-1:.
Proof.
  intros F G u. split; intros H1.
  - destruct H1 as [x [z [H1 H2]]].
    apply ComposeCharac2 in H2. destruct H2 as [y [H2 H3]].
    exists z. exists y. exists x. split.
    + assumption.
    + split; apply ConverseCharac2; assumption.
  - destruct H1 as [z [y [x [H1 [H2 H3]]]]].
    apply (proj1 (ConverseCharac2 _ _ _)) in H2.
    apply (proj1 (ConverseCharac2 _ _ _)) in H3.
    exists x. exists z. split. 1: assumption.
    apply ComposeCharac2. exists y. split; assumption.
Qed.

(* The domain of the composition is a subclass of the first domain.             *)
Proposition ComposeDomainIsSmaller : forall (F G:Class),
  domain (G :.: F) :<=: domain F.
Proof.
  intros F G x H1. destruct H1 as [z H1]. apply ComposeCharac2 in H1.
  destruct H1 as [y [H1 H2]]. exists y. assumption.
Qed.

(* The range of the composition is a subclass of the second range.              *)
Proposition ComposeRangeIsSmaller : forall (F G:Class),
  range (G :.: F) :<=: range G.
Proof.
  intros F G z H1. destruct H1 as [x H1]. apply ComposeCharac2 in H1.
  destruct H1 as [y [H1 H2]]. exists y. assumption.
Qed.

(* The domain of the composition is the same as the first domain if range ok.   *)
Proposition ComposeDomainIsSame : forall (F G:Class),
  range F :<=: domain G -> domain (G :.: F) :~: domain F.
Proof.
  intros F G H1. apply DoubleInclusion. split.
  - apply ComposeDomainIsSmaller.
  - intros x H2. destruct H2 as [y H2].
    assert (domain G y) as H3. { apply H1. exists x. assumption. }
    destruct H3 as [z H3]. exists z. apply ComposeCharac2. exists y.
    split; assumption.
Qed.

(* If first class is functional, same domains conversely implies range is ok.   *)
Proposition ComposeDomainIsSame2 : forall (F G:Class), Functional F ->
  range F :<=: domain G <-> domain (G :.: F) :~: domain F.
Proof.
  intros F G H1. split.
  - apply ComposeDomainIsSame.
  - intros H2 y H3. destruct H3 as [x H3].
    assert (domain (G :.: F) x) as H4. { apply H2. exists y. assumption. }
    destruct H4 as [z H4]. apply ComposeCharac2 in H4. destruct H4 as [y' [H4 H5]].
    assert (y' = y) as H6. { apply H1 with x; assumption. }
    subst. exists z. assumption.
Qed.

(* The range of the composition is the same as the second range if domain ok.   *)
Proposition ComposeRangeIsSame : forall (F G:Class),
  domain G :<=: range F -> range (G :.: F) :~: range G.
Proof.
  intros F G H1. apply DoubleInclusion. split.
  - apply ComposeRangeIsSmaller.
  - intros z H2. destruct H2 as [y H2].
    assert (range F y) as H3. { apply H1. exists z. assumption. }
    destruct H3 as [x H3]. exists x. apply ComposeCharac2. exists y.
    split; assumption.
Qed.

(* If converse of second class is functional, then conversely ...               *)
Proposition ComposeRangeIsSame2 : forall (F G:Class), Functional G^:-1: ->
  domain G :<=: range F <-> range (G :.: F) :~: range G.
Proof.
  intros F G H1. split.
  - apply ComposeRangeIsSame.
  - intros H2 y H3. destruct H3 as [z H3].
    assert (range (G :.: F) z) as H4. { apply H2. exists y. assumption. }
    destruct H4 as [x H4]. apply ComposeCharac2 in H4.
    destruct H4 as [y' [H4 H5]]. assert (y' = y) as H6. {
      apply H1 with z; apply ConverseCharac2; assumption. }
    subst. exists x. assumption.
Qed.

(* Characterisation of the domain of G.F in terms of the eval F!a.              *)
Proposition FunctionalAtComposeDomainCharac : forall (F G:Class) (a:U),
  FunctionalAt F a -> domain (G :.: F) a <-> domain F a /\ domain G F!a.
Proof.
  intros F G a H1. split; intros H2.
  - split.
    + apply ComposeDomainIsSmaller with G. assumption.
    + destruct H2 as [z H2]. apply ComposeCharac2 in H2.
      destruct H2 as [y [H2 H3]]. exists z.
      assert (F!a = y) as H4. {
        apply FunctionalAtEvalCharac. 1: assumption. 2: assumption.
        exists y. assumption.
      }
      rewrite H4. assumption.
  - destruct H2 as [H2 H3]. assert (H4 := H2).
    destruct H2 as [y H2]. destruct H3 as [z H3].
    exists z. apply ComposeCharac2. exists y.
    split. 1: assumption.
    assert (F!a = y) as H5. { apply FunctionalAtEvalCharac; assumption. }
    rewrite <- H5. assumption.
Qed.

Proposition FunctionalComposeDomainCharac : forall (F G:Class) (a:U),
  Functional F -> domain (G :.: F) a <-> domain F a /\ domain G F!a.
Proof.
  intros F G a H1.
  apply FunctionalAtComposeDomainCharac, IsFunctionalAt. assumption.
Qed.

(* G.F is functional at a if F is, G is functional at F!a and a lies in domain. *)
Proposition ComposeIsFunctionalAt : forall (F G:Class) (a:U),
  FunctionalAt F a          ->
  FunctionalAt G (F!a)      ->
  domain F a                ->
  FunctionalAt (G :.: F) a.
Proof.
  intros F G a H1 H2 H3 z1 z2 H4 H5.
  apply ComposeCharac2 in H4. destruct H4 as [y1 [H4 H6]].
  apply ComposeCharac2 in H5. destruct H5 as [y2 [H5 H7]].
  assert (F!a = y1) as H8. { apply FunctionalAtEvalCharac; assumption. }
  assert (F!a = y2) as H9. { apply FunctionalAtEvalCharac; assumption. }
  subst. apply H2; assumption.
Qed.

(* Evaluating the composed class G.F at a, from evaluations of F and G.         *)
Proposition FunctionalAtComposeEval : forall (F G:Class) (a:U),
  FunctionalAt F a        ->
  FunctionalAt G (F!a)    ->
  domain F a              ->
  domain G (F!a)          ->
  (G :.: F)!a = G!(F!a).
Proof.
  intros F G a H1 H2 H3 H4. assert (H5 := H3). assert (H6 := H4).
  destruct H3 as [y H3]. destruct H4 as [z H4].
  assert (F!a = y) as H7. { apply FunctionalAtEvalCharac; assumption. }
  assert (G!(F!a) = z) as H8. { apply FunctionalAtEvalCharac; assumption. }
  assert (FunctionalAt (G :.: F) a) as H9. {
    apply ComposeIsFunctionalAt; assumption. }
  assert ((G :.: F) :(a,z):) as H10. {
    apply ComposeCharac2. exists y. split. 1: assumption. rewrite <- H7. assumption. }
  apply FunctionalAtEvalCharac. 1: assumption.
  - apply FunctionalAtComposeDomainCharac. 1: assumption. split; assumption.
  - rewrite H8. assumption.
Qed.

(* Evaluating the composed class G.F at a, from evaluations of F and G.         *)
Proposition FunctionalComposeEval : forall (F G:Class) (a:U),
  Functional F    ->
  Functional G    ->
  domain F a      ->
  domain G (F!a)  ->
  (G :.: F)!a = G!(F!a).
Proof.
  intros F G a H1 H2. apply FunctionalAtComposeEval.
  - apply IsFunctionalAt. assumption.
  - apply IsFunctionalAt. assumption.
Qed.
