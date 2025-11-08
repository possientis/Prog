Require Import ZF.Class.Bounded.
Require Import ZF.Class.Equiv.
Require Import ZF.Class.Incl.
Require Import ZF.Class.Prod.
Require Import ZF.Class.Relation.Cmp.
Require Import ZF.Class.Relation.Converse.
Require Import ZF.Class.Relation.Domain.
Require Import ZF.Class.Relation.Functional.
Require Import ZF.Class.Relation.FunctionalAt.
Require Import ZF.Class.Relation.Image.
Require Import ZF.Class.Relation.Range.
Require Import ZF.Class.Relation.Relation.
Require Import ZF.Class.Small.
Require Import ZF.Set.Core.
Require Import ZF.Set.Relation.EvalOfClass.
Require Import ZF.Set.OrdPair.

Require Import ZF.Notation.Dot.
Export ZF.Notation.Dot.


(* Composition of two classes.                                                  *)
Definition compose (G F:Class) : Class := fun u =>
  exists x y z, u = :(x,z): /\ F :(x,y): /\ G :(y,z):.

(* Notation "G :.: F" := (compose G F)                                          *)
Global Instance ClassDot : Dot Class := { dot := compose }.

Proposition Charac2 : forall (F G:Class) (x z:U),
  (G :.: F) :(x,z): <-> exists y, F :(x,y): /\ G :(y,z):.
Proof.
  intros F G x z. split; intros H1.
  - destruct H1 as [x' [y [z' [H1 [H2 H3]]]]].
    apply WhenEqual in H1. destruct H1 as [H1 G1]. subst. exists y.
    split; assumption.
  - destruct H1 as [y [H1 H2]]. exists x. exists y. exists z. split.
    + reflexivity.
    + split; assumption.
Qed.

(* Composition is compatible with class equivalence.                            *)
Proposition EquivCompat : forall (F F' G G':Class),
  F :~: F' -> G :~: G' -> G :.: F :~: G' :.: F'.
Proof.
  intros F F' G G' H1 H2 u. split; intros H3;
  destruct H3 as [x [y [z [H3 [H4 H5]]]]]; subst;
  apply Charac2; exists y; split.
  - apply H1. assumption.
  - apply H2. assumption.
  - apply H1. assumption.
  - apply H2. assumption.
Qed.

(* Composition is left-compatible with class equivalence.                       *)
Proposition EquivCompatL : forall (F G G':Class),
  G :~: G' -> G :.: F :~: G' :.: F.
Proof.
  intros F G G' H1. apply EquivCompat.
  - apply Equiv.Refl.
  - assumption.
Qed.

(* Composition is right-compatible with class equivalence.                      *)
Proposition EquivCompatR : forall (F F' G:Class),
  F :~: F' -> G :.: F :~: G :.: F'.
Proof.
  intros F F' G H1. apply EquivCompat.
  - assumption.
  - apply Equiv.Refl.
Qed.

Proposition Assoc : forall (F G H:Class),
  (H :.: G) :.: F :~: H :.: (G :.: F).
Proof.
  intros F G H u. split; intros H1.
 - destruct H1 as [x [y [t [H1 [H2 H3]]]]]. apply Charac2 in H3.
    destruct H3 as [z [H3 H4]].
    exists x. exists z. exists t. split. 1: assumption. split. 2: assumption.
    apply Charac2. exists y. split; assumption.
  - destruct H1 as [x [z [t [H1 [H2 H3]]]]]. apply Charac2 in H2.
    destruct H2 as [y [H2 H4]].
    exists x. exists y. exists t. split. 1: assumption. split. 1: assumption.
    apply Charac2. exists z. split; assumption.
Qed.

(* The composition of two classes is a relation.                                *)
Proposition IsRelation : forall (F G:Class), Relation (G :.: F).
Proof.
  intros F G u [x [y [z [H1 [H2 H3]]]]]. exists x. exists z. assumption.
Qed.

(* The composition of two functional classes is functional.                     *)
Proposition IsFunctional : forall (F G:Class),
  Functional F -> Functional G -> Functional (G :.: F).
Proof.
  intros F G H1 H2 x z1 z2 H3 H4.
  apply Charac2 in H3. destruct H3 as [y1 [H3 H5]].
  apply Charac2 in H4. destruct H4 as [y2 [H4 H6]].
  assert (y1 = y2) as H7. { apply H1 with x; assumption. }
  subst. apply H2 with y2; assumption.
Qed.

(* The converse of the composition is (almost) the composition of the converse. *)
Proposition Converse : forall (F G:Class),
  (G :.: F)^:-1: :~: F^:-1: :.: G^:-1:.
Proof.
  intros F G u. split; intros H1.
  - destruct H1 as [x [z [H1 H2]]].
    apply Charac2 in H2. destruct H2 as [y [H2 H3]].
    exists z. exists y. exists x. split.
    + assumption.
    + split; apply Converse.Charac2Rev; assumption.
  - destruct H1 as [z [y [x [H1 [H2 H3]]]]].
    apply Converse.Charac2 in H2. apply Converse.Charac2 in H3.
    exists x. exists z. split. 1: assumption.
    apply Charac2. exists y. split; assumption.
Qed.

(* The domain of the composition is a subclass of the first domain.             *)
Proposition DomainIsSmaller : forall (F G:Class),
  domain (G :.: F) :<=: domain F.
Proof.
  intros F G x H1. destruct H1 as [z H1]. apply Charac2 in H1.
  destruct H1 as [y [H1 H2]]. exists y. assumption.
Qed.

(* The range of the composition is a subclass of the second range.              *)
Proposition RangeIsSmaller : forall (F G:Class),
  range (G :.: F) :<=: range G.
Proof.
  intros F G z H1. destruct H1 as [x H1]. apply Charac2 in H1.
  destruct H1 as [y [H1 H2]]. exists y. assumption.
Qed.

(* The domain of the composition is the same as the first domain if range ok.   *)
Proposition DomainIsSame : forall (F G:Class),
  range F :<=: domain G -> domain (G :.: F) :~: domain F.
Proof.
  intros F G H1. apply DoubleInclusion. split.
  - apply DomainIsSmaller.
  - intros x H2. destruct H2 as [y H2].
    assert (domain G y) as H3. { apply H1. exists x. assumption. }
    destruct H3 as [z H3]. exists z. apply Charac2. exists y.
    split; assumption.
Qed.

(* If first class is functional, same domains conversely implies range is ok.   *)
Proposition DomainIsSame2 : forall (F G:Class), Functional F ->
  range F :<=: domain G <-> domain (G :.: F) :~: domain F.
Proof.
  intros F G H1. split.
  - apply DomainIsSame.
  - intros H2 y H3. destruct H3 as [x H3].
    assert (domain (G :.: F) x) as H4. { apply H2. exists y. assumption. }
    destruct H4 as [z H4]. apply Charac2 in H4. destruct H4 as [y' [H4 H5]].
    assert (y' = y) as H6. { apply H1 with x; assumption. }
    subst. exists z. assumption.
Qed.

(* The range of the composition is the same as the second range if domain ok.   *)
Proposition RangeIsSame : forall (F G:Class),
  domain G :<=: range F -> range (G :.: F) :~: range G.
Proof.
  intros F G H1. apply DoubleInclusion. split.
  - apply RangeIsSmaller.
  - intros z H2. destruct H2 as [y H2].
    assert (range F y) as H3. { apply H1. exists z. assumption. }
    destruct H3 as [x H3]. exists x. apply Charac2. exists y.
    split; assumption.
Qed.

(* If converse of second class is functional, then conversely ...               *)
Proposition RangeIsSame2 : forall (F G:Class), Functional G^:-1: ->
  domain G :<=: range F <-> range (G :.: F) :~: range G.
Proof.
  intros F G H1. split.
  - apply RangeIsSame.
  - intros H2 y H3. destruct H3 as [z H3].
    assert (range (G :.: F) z) as H4. { apply H2. exists y. assumption. }
    destruct H4 as [x H4]. apply Charac2 in H4.
    destruct H4 as [y' [H4 H5]]. assert (y' = y) as H6. {
      apply H1 with z; apply Converse.Charac2Rev; assumption. }
    subst. exists x. assumption.
Qed.

(* Characterisation of the domain of G.F in terms of the eval F!a.              *)
Proposition FunctionalAtDomainCharac : forall (F G:Class) (a:U),
  FunctionalAt F a -> domain (G :.: F) a <-> domain F a /\ domain G F!a.
Proof.
  intros F G a H1. split; intros H2.
  - split.
    + apply DomainIsSmaller with G. assumption.
    + destruct H2 as [z H2]. apply Charac2 in H2.
      destruct H2 as [y [H2 H3]]. exists z.
      assert (F!a = y) as H4. {
        apply FunctionalAtEvalCharac. 1: assumption. 2: assumption.
        exists y. assumption.
      }
      rewrite H4. assumption.
  - destruct H2 as [H2 H3]. assert (H4 := H2).
    destruct H2 as [y H2]. destruct H3 as [z H3].
    exists z. apply Charac2. exists y.
    split. 1: assumption.
    assert (F!a = y) as H5. { apply FunctionalAtEvalCharac; assumption. }
    rewrite <- H5. assumption.
Qed.

Proposition FunctionalDomainCharac : forall (F G:Class) (a:U),
  Functional F -> domain (G :.: F) a <-> domain F a /\ domain G F!a.
Proof.
  intros F G a H1.
  apply FunctionalAtDomainCharac, IsFunctionalAt. assumption.
Qed.

(* G.F is functional at a if F is, G is functional at F!a and a lies in domain. *)
Proposition IsFunctionalAt : forall (F G:Class) (a:U),
  FunctionalAt F a          ->
  FunctionalAt G (F!a)      ->
  domain F a                ->
  FunctionalAt (G :.: F) a.
Proof.
  intros F G a H1 H2 H3 z1 z2 H4 H5.
  apply Charac2 in H4. destruct H4 as [y1 [H4 H6]].
  apply Charac2 in H5. destruct H5 as [y2 [H5 H7]].
  assert (F!a = y1) as H8. { apply FunctionalAtEvalCharac; assumption. }
  assert (F!a = y2) as H9. { apply FunctionalAtEvalCharac; assumption. }
  subst. apply H2; assumption.
Qed.

(* Evaluating the composed class G.F at a, from evaluations of F and G.         *)
Proposition FunctionalAtEval : forall (F G:Class) (a:U),
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
    apply IsFunctionalAt; assumption. }
  assert ((G :.: F) :(a,z):) as H10. {
    apply Charac2. exists y. split. 1: assumption. rewrite <- H7. assumption. }
  apply FunctionalAtEvalCharac. 1: assumption.
  - apply FunctionalAtDomainCharac. 1: assumption. split; assumption.
  - rewrite H8. assumption.
Qed.

(* Evaluating the composed class G.F at a, from evaluations of F and G.         *)
Proposition Eval : forall (F G:Class) (a:U),
  Functional F    ->
  Functional G    ->
  domain F a      ->
  domain G (F!a)  ->
  (G :.: F)!a = G!(F!a).
Proof.
  intros F G a H1 H2. apply FunctionalAtEval.
  - apply Functional.IsFunctionalAt. assumption.
  - apply Functional.IsFunctionalAt. assumption.
Qed.

Lemma ImageByCmp : forall (F G:Class),
  (G :.: F) :<=: Cmp :[F :x: G]:.
Proof.
  intros F G u H1. destruct H1 as [x [y [z [H1 [H2 H3]]]]].
  exists :(:(x,y):,:(y,z):):. split.
  - apply Prod.Charac2. split; assumption.
  - apply Cmp.Charac2. exists x. exists y. exists y. exists z.
    split. 2: assumption. reflexivity.
Qed.

Proposition IsSmall : forall (F G:Class),
  Small F -> Small G -> Small (G :.: F).
Proof.
  intros F G H1 H2. apply Bounded.WhenSmaller with (Cmp :[F :x: G]:).
  - apply ImageByCmp.
  - apply Image.IsSmall.
    + apply Cmp.IsFunctional.
    + apply Prod.IsSmall; assumption.
Qed.

