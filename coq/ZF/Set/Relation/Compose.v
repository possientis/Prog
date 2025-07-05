Require Import ZF.Class.Equiv.
Require Import ZF.Class.Relation.Compose.
Require Import ZF.Class.Small.
Require Import ZF.Set.Core.
Require Import ZF.Set.FromClass.
Require Import ZF.Set.Incl.
Require Import ZF.Set.OrdPair.
Require Import ZF.Set.Relation.Converse.
Require Import ZF.Set.Relation.Domain.
Require Import ZF.Set.Relation.Eval.
Require Import ZF.Set.Relation.Functional.
Require Import ZF.Set.Relation.Range.
Require Import ZF.Set.Relation.Relation.

Export ZF.Notation.Dot.

(* Composition of two sets.                                                     *)
Definition compose (g f:U) : U := fromClass (toClass g :.: toClass f)
  (Compose.IsSmall (toClass f) (toClass g) (SetIsSmall f) (SetIsSmall g)).

(* Notation "g :.: f" := (compose g f)                                          *)
Global Instance SetDot : Dot U := { dot := compose }.

(* The class of the composition is the composition of the classes.              *)
Proposition ToClass : forall (f g:U),
  toClass (g :.: f) :~: toClass g :.: toClass f.
Proof.
  intros f g. apply ToFromClass.
Qed.

Proposition Charac : forall (f g u:U),
  u :< g :.: f <-> exists x y z, u =:(x,z): /\ :(x,y): :< f /\ :(y,z): :< g.
Proof.
  intros f g u. split; intros H1.
  - apply FromClass.Charac in H1. destruct H1 as [x [y [z [H1 [H2 H3]]]]].
    exists x. exists y. exists z. split. 1: assumption. split; assumption.
  - destruct H1 as [x [y [z [H1 [H2 H3]]]]]. apply FromClass.Charac.
    exists x. exists y. exists z. split. 1: assumption. split; assumption.
Qed.

Proposition Charac2 : forall (f g x z:U),
  :(x,z): :< g :.: f <-> exists y, :(x,y): :< f /\ :(y, z): :< g.
Proof.
  intros f g x z. split; intros H1.
  - apply Charac in H1. destruct H1 as [x' [y [z' [H1 [H2 H3]]]]].
    apply OrdPair.WhenEqual in H1. destruct H1 as [H1 H4]. subst.
    exists y. split; assumption.
  - destruct H1 as [y [H1 H2]]. apply Charac. exists x. exists y. exists z.
    split. 1: reflexivity. split; assumption.
Qed.

(* The composition of two sets is a relation.                                   *)
Proposition IsRelation : forall (f g:U), Relation (g :.: f).
Proof.
  intros f g u H1. apply Charac in H1. destruct H1 as [x [y [z [H1 _]]]].
  exists x. exists z. assumption.
Qed.

Proposition IsFunctional : forall (f g:U),
  Functional f -> Functional g -> Functional (g :.: f).
Proof.
  intros f g H1 H2 x z1 z2 H3 H4. apply Charac2 in H3. apply Charac2 in H4.
  destruct H3 as [y1 [H3 H5]]. destruct H4 as [y2 [H4 H6]].
  assert (y2 = y1) as H7. { apply H1 with x; assumption. }
  subst. apply H2 with y1; assumption.
Qed.

(* The converse of the composition is (almost) the composition of the converse. *)
Proposition Converse : forall (f g:U),
  (g :.: f)^:-1: = f^:-1: :.: g^:-1:.
Proof.
  intros f g. apply DoubleInclusion. split; intros u H1.
  - apply Converse.Charac in H1. destruct H1 as [x [z [H1 H2]]].
    apply Charac2 in H2. destruct H2 as [y [H2 H3]]. apply Charac.
    exists z. exists y. exists x. split. 1: assumption. split;
    apply Converse.Charac2Rev; assumption.
  - apply Charac in H1. destruct H1 as [z [y [x [H1 [H2 H3]]]]].
    apply Converse.Charac2 in H2. apply Converse.Charac2 in H3.
    apply Converse.Charac. exists x. exists z. split. 1: assumption.
    apply Charac2. exists y. split; assumption.
Qed.

(* The domain of the composition is a subset of the first domain.               *)
Proposition DomainIsSmaller : forall (f g:U),
  domain (g :.: f) :<=: domain f.
Proof.
  intros f g x H1. apply Domain.Charac in H1. destruct H1 as [z H1].
  apply Charac2 in H1. destruct H1 as [y [H1 _]].
  apply Domain.Charac. exists y. assumption.
Qed.

(* The range of the composition is a subset of the second range.                *)
Proposition RangeIsSmaller : forall (f g:U),
  range (g :.: f) :<=: range g.
Proof.
  intros f g z H1. apply Range.Charac in H1. destruct H1 as [x H1].
  apply Charac2 in H1. destruct H1 as [y [_ H1]].
  apply Range.Charac. exists y. assumption.
Qed.

(* The domain of the composition is the same as the first domain if range ok.   *)
Proposition DomainIsSame : forall (f g:U),
  range f :<=: domain g -> domain (g :.: f) = domain f.
Proof.
  intros f g H1. apply DoubleInclusion. split.
  - apply DomainIsSmaller.
  - intros x H2. apply Domain.Charac in H2. destruct H2 as [y H2].
    assert (y :< domain g) as H3. {
      apply H1. apply Range.Charac. exists x. assumption. }
    apply Domain.Charac in H3. destruct H3 as [z H3].
    apply Domain.Charac. exists z. apply Charac2. exists y. split; assumption.
Qed.

(* If first set is functional, same domains conversely implies range is ok.     *)
Proposition DomainIsSame2 : forall (f g:U), Functional f ->
  range f :<=: domain g <-> domain (g :.: f) = domain f.
Proof.
  intros f g H1. split.
  - apply DomainIsSame.
  - intros H2 y H3. apply Range.Charac in H3. destruct H3 as [x H3].
    assert (x :< domain (g :.: f)) as H4. {
      rewrite H2. apply Domain.Charac. exists y. assumption. }
    apply Domain.Charac in H4. destruct H4 as [z H4].
    apply Charac2 in H4. destruct H4 as [y' [H4 H5]].
    assert (y' = y) as H6. { apply H1 with x; assumption. }
    subst. apply Domain.Charac. exists z. assumption.
Qed.

(* The range of the composition is the same as the second range if domain ok.   *)
Proposition RangeIsSame : forall (f g:U),
  domain g :<=: range f -> range (g :.: f) = range g.
Proof.
  intros f g H1. apply DoubleInclusion. split.
  - apply RangeIsSmaller.
  - intros z H2. apply Range.Charac in H2. destruct H2 as [y H2].
    assert (y :< range f) as H3. {
      apply H1. apply Domain.Charac. exists z. assumption. }
    apply Range.Charac in H3. destruct H3 as [x H3].
    apply Range.Charac. exists x. apply Charac2. exists y. split; assumption.
Qed.

(* If converse of second set is functional, then conversely ...                 *)
Proposition RangeIsSame2 : forall (f g:U), Functional g^:-1: ->
  domain g :<=: range f <-> range (g :.: f) = range g.
Proof.
  intros f g H1. split.
  - apply RangeIsSame.
  - intros H2 y H3. apply Domain.Charac in H3. destruct H3 as [z H3].
    assert (z :< range (g :.: f)) as H4. {
      rewrite H2. apply Range.Charac. exists y. assumption. }
    apply Range.Charac in H4. destruct H4 as [x H4].
    apply Charac2 in H4. destruct H4 as [y' [H4 H5]].
    assert (y' = y) as H6. {
      apply Converse.WhenFunctional with g z; assumption. }
    subst. apply Range.Charac. exists x. assumption.
Qed.

Proposition FunctionalDomainCharac : forall (f g x:U),
  Functional f -> x :< domain (g :.: f) <-> x :< domain f /\ f!x :< domain g.
Proof.
  intros f g x H1. split; intros H2.
  - apply Domain.Charac in H2. destruct H2 as [z H2].
    apply Charac2 in H2. destruct H2 as [y [H2 H3]].
    assert (x :< domain f) as H4. { apply Domain.Charac. exists y. assumption. }
    assert (f!x = y) as H5. { apply Eval.Charac; assumption. }
    split. 1: assumption. rewrite H5. apply Domain.Charac. exists z. assumption.
  - destruct H2 as [H2 H3]. apply Domain.Charac in H2. destruct H2 as [y H2].
    assert (x :< domain f) as H4. { apply Domain.Charac. exists y. assumption. }
    assert (f!x = y) as H5. { apply Eval.Charac; assumption. }
    rewrite H5 in H3. apply Domain.Charac in H3. destruct H3 as [z H3].
    apply Domain.Charac. exists z. apply Charac2. exists y. split; assumption.
Qed.

Proposition Eval : forall (f g x:U),
  Functional f      ->
  Functional g      ->
  x :< domain f     ->
  f!x :< domain g   ->
  (g :.: f)!x = g!(f!x).
Proof.
  intros f g x H1 H2 H3 H4. assert (H5 := H3).
  apply Domain.Charac in H5. destruct H5 as [y H5].
  assert (f!x = y) as H6. { apply Eval.Charac; assumption. }
  rewrite H6 in H4. assert (H7 := H4).
  apply Domain.Charac in H7. destruct H7 as [z H7]. rewrite H6.
  assert (g!y = z) as H8. { apply Eval.Charac; assumption. }
  rewrite H8. apply Eval.Charac.
  - apply IsFunctional; assumption.
  - apply Domain.Charac. exists z. apply Charac2. exists y. split; assumption.
  - apply Charac2. exists y. split; assumption.
Qed.
