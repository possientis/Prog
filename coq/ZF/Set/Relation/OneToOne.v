Require Import ZF.Set.Core.
Require Import ZF.Set.Incl.
Require Import ZF.Set.OrdPair.
Require Import ZF.Set.Relation.Compose.
Require Import ZF.Set.Relation.Converse.
Require Import ZF.Set.Relation.Domain.
Require Import ZF.Set.Relation.Eval.
Require Import ZF.Set.Relation.Functional.
Require Import ZF.Set.Relation.Image.
Require Import ZF.Set.Relation.InvImage.
Require Import ZF.Set.Relation.Range.
Require Import ZF.Set.Relation.Restrict.

(* A set is one-to-one iff both itself and its converse are functional.         *)
Definition OneToOne (f:U) : Prop := Functional f /\ Functional f^:-1:.


(* Uniqueness of left coordinate when one-to-one.                               *)
Proposition CharacL : forall (f:U), OneToOne f ->
  forall x y z, :(y,x): :< f -> :(z,x): :< f -> y = z.
Proof.
  intros f [_ H1] x y z H2 H3.
  apply H1 with x; apply Converse.Charac2Rev; assumption.
Qed.

(* Uniqueness of right coordinate when one-to-one.                              *)
Proposition CharacR : forall (f:U), OneToOne f ->
  forall x y z, :(x,y): :< f -> :(x,z): :< f -> y = z.
Proof.
  intros f [H1 _]. assumption.
Qed.

(* When two ordered pairs belong to a one-to-one set, equality between the      *)
(* first coordinates is equivalent to equality between the second coordinates.  *)
Proposition CoordEquiv : forall (f:U) (x1 x2 y1 y2:U),
  OneToOne f -> :(x1,y1): :< f -> :(x2,y2): :< f -> x1 = x2 <-> y1 = y2.
Proof.
  intros f x1 x2 y1 y2 H3 H1 H2. split; intros H4; subst.
  - apply CharacR with f x2; assumption.
  - apply CharacL with f y2; assumption.
Qed.

Proposition Converse : forall (f:U),
  OneToOne f -> OneToOne f^:-1:.
Proof.
  intros f [H1 H2]. split. 1: assumption. apply Functional.InclCompat with f.
  2: assumption. apply Converse.IsIncl.
Qed.

Proposition EvalCharac : forall (f x y:U),
  OneToOne f -> x :< domain f -> :(x,y): :< f  <-> f!x = y.
Proof.
  intros f x y [H1 _]. apply Eval.Charac. assumption.
Qed.

Proposition Satisfies : forall (f x:U),
  OneToOne f -> x :< domain f -> :(x,f!x): :< f.
Proof.
  intros f x [H1 _]. apply Eval.Satisfies. assumption.
Qed.

Proposition IsInRange : forall (f x:U),
  OneToOne f -> x :< domain f -> f!x :< range f.
Proof.
  intros f x [H1 _]. apply Eval.IsInRange. assumption.
Qed.

Proposition ImageCharac : forall (f a:U), OneToOne f ->
  forall y, y :< f:[a]: <-> exists x, x :< a /\ x :< domain f /\ f!x = y.
Proof.
  intros f a [H1 _]. apply Eval.ImageCharac. assumption.
Qed.

Proposition ConverseEvalIsInDomain : forall (f y:U),
  OneToOne f -> y :< range f -> f^:-1:!y :< domain f.
Proof.
  intros f y H1 H2. rewrite <- Converse.Range. apply IsInRange.
  - apply Converse. assumption.
  - rewrite Converse.Domain. assumption.
Qed.

(* The composition of two one-to-one sets is one-to-one.                        *)
Proposition Compose : forall (f g:U),
  OneToOne f -> OneToOne g -> OneToOne (g :.: f).
Proof.
  intros f g [H1 H2] [H3 H4]. split.
  - apply Compose.IsFunctional; assumption.
  - rewrite Compose.Converse. apply Compose.IsFunctional; assumption.
Qed.

Proposition ConverseEvalOfEval : forall (f x:U),
  OneToOne f -> x :< domain f -> f^:-1:!(f!x) = x.
Proof.
  intros f x [H1 H2] H3. apply Eval.Charac. 1: assumption.
  - rewrite Converse.Domain. apply Range.Charac. exists x.
    apply Eval.Satisfies; assumption.
  - apply Converse.Charac2Rev, Eval.Satisfies; assumption.
Qed.

Proposition EvalOfConverseEval : forall (f y:U),
  OneToOne f -> y :< range f -> f!(f^:-1:!y) = y.
Proof.
  intros f y [H1 H2] H3. assert (H4 := H3). apply Range.Charac in H4.
  destruct H4 as [x H4].
  assert (f^:-1:!y = x) as H5. {
    apply Eval.Charac. 1: assumption.
    - rewrite Converse.Domain. assumption.
    - apply Converse.Charac2Rev. assumption. }
  rewrite H5. apply Eval.Charac; try assumption. apply Domain.Charac.
  exists y. assumption.
Qed.

Proposition DomainOfCompose : forall (f g x:U),
  OneToOne f -> x :< domain (g :.: f) <-> x :< domain f /\ f!x :< domain g.
Proof.
  intros f g x [H1 _]. apply Compose.FunctionalDomainCharac. assumption.
Qed.

Proposition ComposeEval : forall (f g x:U),
  OneToOne f      ->
  OneToOne g      ->
  x   :< domain f ->
  f!x :< domain g ->
  (g :.: f)!x = g!(f!x).
Proof.
  intros f g x [H1 _] [H2 _]. apply Compose.Eval; assumption.
Qed.

Proposition InvImageOfImage : forall (f a:U),
  OneToOne f -> a :<=: domain f -> f^:-1::[ f:[a]: ]: = a.
Proof.
  intros f a [H1 H2] H3. apply DoubleInclusion. split.
  - apply InvImage.OfImageIsLess. assumption.
  - apply InvImage.OfImageIsMore. assumption.
Qed.

Proposition ImageOfInvImage : forall (f b:U),
  OneToOne f -> b :<=: range f -> f:[ f^:-1::[b]: ]: = b.
Proof.
  intros f b [H1 H2] H3. apply DoubleInclusion. split.
  - apply InvImage.ImageIsLess. assumption.
  - apply InvImage.ImageIsMore. assumption.
Qed.

Proposition EvalInjective : forall (f x y:U),
  OneToOne f -> x :< domain f -> y :< domain f -> f!x = f!y -> x = y.
Proof.
  intros f x y H1 H2 H3 H4.
  assert (:(x,f!x): :< f) as H5. { apply Satisfies; assumption. }
  assert (:(y,f!y): :< f) as H6. { apply Satisfies; assumption. }
  rewrite <- H4 in H6. revert H5 H6. apply CharacL. assumption.
Qed.

Proposition WhenFunctional : forall (f:U),
  Functional f                                                        ->
  (forall x y, x :< domain f -> y :< domain f -> f!x = f!y -> x = y)  ->
  OneToOne f.
Proof.
  intros f H1 H2. split. 1: assumption. intros y x1 x2 H3 H4.
  apply Converse.Charac2 in H3. apply Converse.Charac2 in H4.
  assert (x1 :< domain f) as H5. { apply Domain.Charac. exists y. assumption. }
  assert (x2 :< domain f) as H6. { apply Domain.Charac. exists y. assumption. }
  assert (f!x1 = y) as H7. { apply Eval.Charac; assumption. }
  assert (f!x2 = y) as H8. { apply Eval.Charac; assumption. }
  specialize (H2 x1 x2). apply H2; try assumption.
  rewrite H7. symmetry. assumption.
Qed.

Proposition EvalInImage : forall (f a x:U),
  OneToOne f -> x :< domain f -> f!x :< f:[a]: <-> x :< a.
Proof.
  intros f a x H1 H2. split; intros H3.
  - apply Image.Charac in H3. destruct H3 as [x' [H3 H4]].
    assert (x' = x) as H5. {
      apply CharacL with f (f!x); try assumption.
      apply Satisfies; assumption. }
    subst. assumption.
  - apply Image.Charac. exists x. split. 1: assumption.
    apply Satisfies; assumption.
Qed.

Proposition Restrict : forall (f a:U),
  OneToOne f  -> OneToOne (f:|:a).
Proof.
  intros f a [H1 H2]. split.
  - apply Restrict.IsFunctional. assumption.
  - intros z y x H3 H4.
    apply Converse.Charac2 in H3. apply Restrict.Charac2 in H3.
    apply Converse.Charac2 in H4. apply Restrict.Charac2 in H4.
    destruct H3 as [H3 H5]. destruct H4 as [H4 H6].
    apply H2 with z; apply Converse.Charac2Rev; assumption.
Qed.

