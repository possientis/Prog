Require Import ZF.Set.Core.
Require Import ZF.Set.Incl.
Require Import ZF.Set.OrdPair.
Require Import ZF.Set.Prod.
Require Import ZF.Set.Relation.Compose.
Require Import ZF.Set.Relation.Converse.
Require Import ZF.Set.Relation.Domain.
Require Import ZF.Set.Relation.Eval.
Require Import ZF.Set.Relation.Functional.
Require Import ZF.Set.Relation.Image.
Require Import ZF.Set.Relation.InvImage.
Require Import ZF.Set.Relation.Range.
Require Import ZF.Set.Relation.Relation.


(* A set is a function iff it is a relation and it is functional.               *)
Definition Function (f:U) : Prop := Relation f /\ Functional f.

(* Two functions with the same domains which coincide pointwise are equal.      *)
Proposition EqualCharac : forall (f g:U),
  Function f                              ->
  Function g                              ->
  domain f = domain g                     -> 
  (forall x, x :< domain f -> f!x = g!x)  ->
  f = g.
Proof.
  intros f g [H1 H2] [H3 H4] H5 H6. apply DoubleInclusion. split; intros x H7.
  - specialize (H1 x H7). destruct H1 as [y [z H1]]. subst.
    assert (y :< domain f) as H8. { apply Domain.Charac. exists z. assumption. }
    assert (f!y = z) as H9. { apply Eval.Charac; assumption. }
    assert (g!y = z) as H10. { rewrite <- H9. symmetry. apply H6. assumption. }
    rewrite <- H10. apply Eval.Satisfies. 1: assumption.
    rewrite <- H5. assumption. 
  - specialize (H3 x H7). destruct H3 as [y [z H3]]. subst.
    assert (y :< domain g) as H8. { apply Domain.Charac. exists z. assumption. }
    assert (g!y = z) as H9. { apply Eval.Charac; assumption. }
    assert (f!y = z) as H10. { rewrite <- H9. apply H6. rewrite H5. assumption. }
    rewrite <- H10. apply Eval.Satisfies. 1: assumption.
    rewrite H5. assumption.
Qed.

(* The direct image of the domain is the range. f need not be a function.       *)
Proposition ImageOfDomain : forall (f:U),
  f:[domain f]: = range f.
Proof.
  apply Range.ImageOfDomain.
Qed.

(* A function is a subset of the product of its domain and image thereof.       *)
Proposition IsIncl : forall (f:U),
  Function f -> f :<=: (domain f) :x: f:[domain f]:.
Proof.
  intros f H1. apply Relation.IsIncl, H1.
Qed.

(* The inverse image of the range is the domain. f need not be a function.      *)
Proposition InvImageOfRange : forall (f:U),
  f^:-1::[range f]: = domain f.
Proof.
  apply InvImage.OfRange.  
Qed.

(* The composition of two functional sets is a function.                        *)
Proposition FunctionalCompose : forall (f g:U),
  Functional f -> Functional g -> Function (g :.: f).
Proof.
  intros f g H1 H2. split.
  - apply Compose.IsRelation.
  - apply Compose.IsFunctional; assumption.
Qed.

(* The composition of two functions is a function.                              *)
Proposition Compose : forall (f g:U),
  Function f -> Function g -> Function (g :.: f).
Proof.
  intros f g [_ H1] [_ H2]. apply FunctionalCompose; assumption.
Qed.

Proposition EvalCharac : forall (f x y:U),
  Function f -> x :< domain f -> :(x,y): :< f <-> f!x = y.
Proof.
  intros f x y H1. apply Eval.Charac, H1.
Qed.

Proposition Satisfies : forall (f x:U),
  Function f -> x :< domain f -> :(x,f!x): :< f.
Proof.
  intros f x H1. apply Eval.Satisfies, H1.
Qed.

Proposition IsInRange : forall (f x:U),
  Function f -> x :< domain f -> f!x :< range f.
Proof.
  intros f x H1. apply Eval.IsInRange, H1.
Qed.

Proposition ImageCharac : forall (f a: U), Function f ->
  forall y, y :< f:[a]: <-> exists x, x :< a /\ x :< domain f /\ f!x = y.
Proof.
  intros f a H1. apply Eval.ImageCharac, H1.
Qed.

Proposition DomainOfCompose : forall (f g x:U),
  Function f -> x :< domain (g :.: f) <-> x :< domain f /\ f!x :< domain g.
Proof.
  intros F G x H1. apply Compose.FunctionalDomainCharac, H1.
Qed.

Proposition ComposeEval : forall (f g x:U),
  Function f      ->
  Function g      ->
  x :< domain f   ->
  f!x :< domain g ->
  (g :.: f)!x = g!(f!x).
Proof.
  intros f g x [_ H1] [_ H2]. apply Compose.Eval; assumption.
Qed.

Proposition RangeCharac : forall (f y:U),
  Function f -> y :< range f <-> exists x, x :< domain f /\ y = f!x.
Proof.
  intros f y H1. split; intros H2.
  - apply Range.Charac in H2. destruct H2 as [x H2]. exists x. split.
    + apply Domain.Charac. exists y. assumption.
    + symmetry. apply EvalCharac; try assumption. apply Domain.Charac. 
      exists y. assumption.
  - destruct H2 as [x [H2 H3]]. 
Admitted.
