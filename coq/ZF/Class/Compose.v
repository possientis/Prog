Require Import ZF.Binary.Compose.
Require Import ZF.Class.
Require Import ZF.Class.Converse.
Require Import ZF.Class.Domain.
Require Import ZF.Class.FromBinary.
Require Import ZF.Class.Function.
Require Import ZF.Class.Functional.
Require Import ZF.Class.FunctionalAt.
Require Import ZF.Class.Image.
Require Import ZF.Class.Incl.
Require Import ZF.Class.OneToOne.
Require Import ZF.Class.Range.
Require Import ZF.Class.Relation.
Require Import ZF.Core.Dot.
Require Import ZF.Set.
Require Import ZF.Set.Eval.
Require Import ZF.Set.OrdPair.
Export ZF.Core.Dot.

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

(* Composition is compatible with class equivalence.                            *)
Proposition ComposeEquivCompat : forall (F F' G G':Class),
  F :~: F' -> G :~: G' -> G :.: F :~: G' :.: F'.
Proof.
  intros F F' G G' H1 H2 u. split; intros H3;
  apply ComposeCharac in H3; destruct H3 as [x [y [z [H3 [H4 H5]]]]]; subst;
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
  - apply ClassEquivRefl.
  - assumption.
Qed.

(* Composition is right-compatible with class equivalence.                      *)
Proposition ComposeEquivCompatR : forall (F F' G:Class),
  F :~: F' -> G :.: F :~: G :.: F'.
Proof.
  intros F F' G H1. apply ComposeEquivCompat.
  - assumption.
  - apply ClassEquivRefl.
Qed.

(* The composition of two classes is a relation.                                *)
Proposition ComposeIsRelation : forall (F G:Class), Relation (G :.: F).
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
  apply FunctionalSuffice. intros x z1 z2 H1 H2.
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
Proposition ComposeConverse : forall (F G:Class),
  (G :.: F)^:-1: :~: F^:-1: :.: G^:-1:.
Proof.
  intros F G u. split; intros H1.
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
Proposition ComposeIsOneToOne : forall (F G:Class),
  OneToOne F -> OneToOne G -> OneToOne (G :.: F).
Proof.
  intros F G H1 H2.
  apply OneToOneCharac in H1. destruct H1 as [H1 H3].
  apply OneToOneCharac in H2. destruct H2 as [H2 H4].
  apply OneToOneCharac. split.
  - apply ComposeIsFunctional; assumption.
  - apply FunctionalEquivCompat with (converse F :.: converse G).
    + apply ClassEquivSym, ComposeConverse.
    + apply ComposeIsFunctional; assumption.
Qed.

(* The domain of the composition is a subclass of the first domain.             *)
Proposition ComposeDomainIsSmaller : forall (F G:Class),
  domain (G :.: F) :<=: domain F.
Proof.
  intros F G x H1. apply (proj1 (DomainCharac _ _)) in H1.
  destruct H1 as [z H1]. apply ComposeCharac2 in H1. destruct H1 as [y [H1 H2]].
  apply DomainCharac. exists y. assumption.
Qed.

(* The range of the composition is a subclass of the second range.              *)
Proposition ComposeRangeIsSmaller : forall (F G:Class),
  range (G :.: F) :<=: range G.
Proof.
  intros F G z H1. apply (proj1 (RangeCharac _ _)) in H1.
  destruct H1 as [x H1]. apply ComposeCharac2 in H1. destruct H1 as [y [H1 H2]].
  apply RangeCharac. exists y. assumption.
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
Proposition ComposeDomainIsSame2 : forall (F G:Class), Functional F ->
  range F :<=: domain G <-> domain (G :.: F) :~: domain F.
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

(* The range of the composition is the same as the second range if domain ok.   *)
Proposition ComposeRangeIsSame : forall (F G:Class),
  domain G :<=: range F -> range (G :.: F) :~: range G.
Proof.
  intros F G H1. apply DoubleInclusion. split.
  - apply ComposeRangeIsSmaller.
  - intros z H2. apply (proj1 (RangeCharac _ _)) in H2. destruct H2 as [y H2].
    assert (range F y) as H3. { apply H1. apply DomainCharac. exists z. assumption. }
    apply (proj1 (RangeCharac _ _)) in H3. destruct H3 as [x H3].
    apply RangeCharac. exists x. apply ComposeCharac2. exists y.
    split; assumption.
Qed.

(* If converse of second class is functional, then conversely ...               *)
Proposition ComposeRangeIsSame2 : forall (F G:Class), Functional G^:-1: ->
  domain G :<=: range F <-> range (G :.: F) :~: range G.
Proof.
  intros F G H1. split.
  - apply ComposeRangeIsSame.
  - intros H2 y H3. apply (proj1 (DomainCharac _ _)) in H3. destruct H3 as [z H3].
    assert (range (G :.: F) z) as H4. { apply H2, RangeCharac. exists y. assumption. }
    apply (proj1 (RangeCharac _ _)) in H4. destruct H4 as [x H4].
    apply ComposeCharac2 in H4. destruct H4 as [y' [H4 H5]].
    assert (y' = y) as H6. {
      apply FunctionalCharac1 with (converse G) z. 1: assumption.
      - apply ConverseCharac2. assumption.
      - apply ConverseCharac2. assumption.
    } subst. apply RangeCharac. exists x. assumption.
Qed.

(* Characterisation of the domain of G.F in terms of the eval F!a.              *)
Proposition ComposeDomainEvalCharac : forall (F G:Class) (a:U),
  FunctionalAt F a -> domain (G :.: F) a <-> domain F a /\ domain G F!a.
Proof.
  intros F G a H1. split; intros H2.
  - split.
    + apply ComposeDomainIsSmaller with G. assumption.
    + apply (proj1 (DomainCharac _ _)) in H2. destruct H2 as [z H2].
      apply ComposeCharac2 in H2. destruct H2 as [y [H2 H3]].
      apply DomainCharac. exists z.
      assert (F!a = y) as H4. {
        apply EvalWhenFunctionalAt. 1: assumption. 2: assumption.
        apply DomainCharac. exists y. assumption.
      }
      rewrite H4. assumption.
  - destruct H2 as [H2 H3]. assert (H4 := H2).
    apply (proj1 (DomainCharac _ _)) in H2. destruct H2 as [y H2].
    apply (proj1 (DomainCharac _ _)) in H3. destruct H3 as [z H3].
    apply DomainCharac. exists z. apply ComposeCharac2. exists y.
    split. 1: assumption.
    assert (F!a = y) as H5. { apply EvalWhenFunctionalAt; assumption. }
    rewrite <- H5. assumption.
Qed.

(* G.F is functional at a if F is, G is functional at F!a and a lies in domain. *)
Proposition ComposeIsFunctionalAt : forall (F G:Class) (a:U),
  FunctionalAt F a          ->
  FunctionalAt G (F!a)      ->
  domain F a                ->
  FunctionalAt (G :.: F) a.
Proof.
  intros F G a H1 H2 H3. apply FunctionalAtCharac2. intros z1 z2 H4 H5.
  apply ComposeCharac2 in H4. destruct H4 as [y1 [H4 H6]].
  apply ComposeCharac2 in H5. destruct H5 as [y2 [H5 H7]].
  assert (F!a = y1) as H8. { apply EvalWhenFunctionalAt; assumption. }
  assert (F!a = y2) as H9. { apply EvalWhenFunctionalAt; assumption. }
  subst. apply FunctionalAtCharac1 with G (F!a); assumption.
Qed.

(* Evaluating the composed class G.F at a, from evaluations of F and G.         *)
Proposition ComposeEvalAt : forall (F G:Class) (a:U),
  FunctionalAt F a        ->
  FunctionalAt G (F!a)    ->
  domain (G :.: F) a      ->
  (G :.: F)!a = G!(F!a).
Proof.
  intros F G a H1 H2 H3. assert (H4 := H3).
  apply ComposeDomainEvalCharac in H4. 2: assumption.
  destruct H4 as [H4 H5]. assert (H6 := H4). assert (H7 := H5).
  apply (proj1 (DomainCharac _ _)) in H4. destruct H4 as [y H4].
  apply (proj1 (DomainCharac _ _)) in H5. destruct H5 as [z H5].
  assert (F!a = y) as H8.     { apply EvalWhenFunctionalAt; assumption. }
  assert (G!(F!a) = z) as H9. { apply EvalWhenFunctionalAt; assumption. }
  assert (FunctionalAt (G :.: F) a) as H10. { apply ComposeIsFunctionalAt; assumption. }
  assert ((G :.: F) :(a,z):) as H11. {
    apply ComposeCharac2. exists y. split. 1: assumption. rewrite <- H8. assumption.
  }
  apply EvalWhenFunctionalAt.
  - assumption.
  - assumption.
  - rewrite H9. assumption.
Qed.

(* Evaluating the composed class G.F at a, from evaluations of F and G.         *)
Proposition ComposeEval : forall (F G:Class) (a:U),
  Functional F -> Functional G -> domain (G :.: F) a -> (G :.: F)!a = G!(F!a).
Proof.
  intros F G a H1 H2 H3. apply ComposeEvalAt.
  - apply FunctionalIsFunctionalAt. assumption.
  - apply FunctionalIsFunctionalAt. assumption.
  - assumption.
Qed.

