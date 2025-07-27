Require Import ZF.Set.Core.
Require Import ZF.Set.Diff.
Require Import ZF.Set.Empty.
Require Import ZF.Set.Incl.
Require Import ZF.Set.Inter2.
Require Import ZF.Set.OrdPair.
Require Import ZF.Set.Prod.
Require Import ZF.Set.Relation.Compose.
Require Import ZF.Set.Relation.Converse.
Require Import ZF.Set.Relation.Domain.
Require Import ZF.Set.Relation.Eval.
Require Import ZF.Set.Relation.Function.
Require Import ZF.Set.Relation.Image.
Require Import ZF.Set.Relation.InvImage.
Require Import ZF.Set.Relation.OneToOne.
Require Import ZF.Set.Relation.Range.
Require Import ZF.Set.Relation.Relation.
Require Import ZF.Set.Relation.Restrict.

(* A set is a bijection iff it is a relation and it is one-to-one.              *)
Definition Bijection (f:U) : Prop := Relation f /\ OneToOne f.

(* A bijection is a function.                                                   *)
Proposition IsFunction : forall (f:U),
  Bijection f -> Function f.
Proof.
  intros f [H1 [H2 _]]. split; assumption.
Qed.

(* Two bijections are equal iff they have same domain and coincide pointwise.   *)
Proposition EqualCharac : forall (f g:U),
  Bijection f                             ->
  Bijection g                             ->
  domain f = domain g                     ->
  (forall x, x :< domain f -> f!x = g!x)  ->
  f = g.
Proof.
  intros f g H1 H2. apply Function.EqualCharac; apply IsFunction; assumption.
Qed.

(* f need not be a bijection.                                                   *)
Proposition ImageOfDomain : forall (f:U),
  f:[domain f]: = range f.
Proof.
  apply Range.ImageOfDomain.
Qed.

Proposition IsIncl : forall (f:U),
  Bijection f -> f :<=: (domain f) :x: f:[domain f]:.
Proof.
  intros f H1. apply Function.IsIncl, IsFunction. assumption.
Qed.

(* The inverse image of the range is the domain. F need not be a bijection.     *)
Proposition InvImageOfRange : forall (f:U),
  f^:-1::[range f]: = domain f.
Proof.
  apply InvImage.OfRange.
Qed.

(* The composition of two one-to-one sets is a bijection.                       *)
Proposition OneToOneCompose : forall (f g:U),
  OneToOne f -> OneToOne g -> Bijection (g :.: f).
Proof.
  intros f g H1 H2. split.
  - apply Compose.IsRelation.
  - apply OneToOne.Compose; assumption.
Qed.

(* The composition of two bijections is a bijection.                            *)
Proposition Compose: forall (f g:U),
  Bijection f -> Bijection g -> Bijection (g :.: f).
Proof.
  intros f g [_ H1] [_ H2]. apply OneToOneCompose; assumption.
Qed.

Proposition EvalCharac : forall (f x y:U),
  Bijection f -> x :< domain f -> :(x,y): :< f <-> f!x = y.
Proof.
  intros f x y H1. apply OneToOne.EvalCharac, H1.
Qed.

Proposition Satisfies : forall (f x:U),
  Bijection f -> x :< domain f -> :(x,f!x): :< f.
Proof.
  intros f x H1. apply OneToOne.Satisfies, H1.
Qed.

Proposition IsInRange : forall (f x:U),
  Bijection f -> x :< domain f -> f!x :< range f.
Proof.
  intros f x H1. apply OneToOne.IsInRange, H1.
Qed.

Proposition ImageCharac : forall (f a:U), Bijection f ->
  forall y, y :< f:[a]: <-> exists x, x :< a /\ x :< domain f /\ f!x = y.
Proof.
  intros f a H1. apply OneToOne.ImageCharac, H1.
Qed.

Proposition DomainOfCompose : forall (f g x:U),
  Bijection f -> x :< domain (g :.: f) <-> x :< domain f /\ f!x :< domain g.
Proof.
  intros f g x H1. apply OneToOne.DomainOfCompose, H1.
Qed.

Proposition ComposeEval : forall (f g x:U),
  Bijection f     ->
  Bijection g     ->
  x   :< domain f ->
  f!x :< domain g ->
  (g :.: f)!x = g!(f!x).
Proof.
  intros f g x [_ H1] [_ H2]. apply OneToOne.ComposeEval; assumption.
Qed.

Proposition RangeCharac : forall (f y:U),
  Bijection f -> y :< range f <-> exists x, x :< domain f /\ f!x = y.
Proof.
  intros f y H1. apply Function.RangeCharac, IsFunction. assumption.
Qed.

(* If the domain of f is not empty, then neither is the range.                  *)
Proposition RangeIsNotEmpty : forall (f:U),
  domain f <> :0: -> range f <> :0:.
Proof.
  apply Range.IsNotEmpty.
Qed.

Proposition IsRestrict : forall (f:U),
  Bijection f -> f = f :|: domain f.
Proof.
  intros f H1. apply Function.IsRestrict, IsFunction. assumption.
Qed.

Proposition ConverseIsFunction : forall (f:U),
  Bijection f -> Function f^:-1:.
Proof.
  intros f [H1 [_ H2]]. split. 2: assumption. apply Converse.IsRelation.
Qed.

Proposition Converse : forall (f:U),
  Bijection f -> Bijection f^:-1:.
Proof.
  intros f [H1 H2]. split.
  - apply Converse.IsRelation.
  - apply OneToOne.Converse. assumption.
Qed.

Proposition ConverseEvalIsInDomain : forall (f y:U),
  Bijection f -> y :< range f -> f^:-1:!y :< domain f.
Proof.
  intros f y H1 H2. rewrite <- Converse.Range. apply IsInRange.
  - apply Converse. assumption.
  - rewrite Converse.Domain. assumption.
Qed.

Proposition ConverseEvalOfEval : forall (f x:U),
  Bijection f -> x :< domain f -> f^:-1:!(f!x) = x.
Proof.
  intros f x H1. apply OneToOne.ConverseEvalOfEval, H1.
Qed.

Proposition EvalOfConverseEval : forall (f y:U),
  Bijection f -> y :< range f -> f!(f^:-1:!y) = y.
Proof.
  intros f y H1. apply OneToOne.EvalOfConverseEval, H1.
Qed.

Proposition InvImageOfImage : forall (f a:U),
  Bijection f -> a :<=: domain f -> f^:-1::[ f:[a]: ]: = a.
Proof.
  intros f a H1. apply OneToOne.InvImageOfImage, H1.
Qed.

Proposition ImageOfInvImage : forall (f b:U),
  Bijection f -> b :<=: range f -> f:[ f^:-1::[b]: ]: = b.
Proof.
  intros f b H1. apply OneToOne.ImageOfInvImage, H1.
Qed.

Proposition EvalInjective : forall (f x y:U),
  Bijection f -> x :< domain f -> y :< domain f -> f!x = f!y -> x = y.
Proof.
  intros f x y H1. apply OneToOne.EvalInjective, H1.
Qed.

Proposition EvalInImage : forall (f a x:U),
  Bijection f -> x :< domain f -> f!x :< f:[a]: <-> x :< a.
Proof.
  intros f a x H1. apply OneToOne.EvalInImage, H1.
Qed.

Proposition Inter2Image : forall (f a b:U),
  Bijection f -> f:[a :/\: b]: = f:[a]: :/\: f:[b]:.
Proof.
  intros f a b H1. apply Converse.Inter2Image, H1.
Qed.

Proposition DiffImage : forall (f a b:U),
  Bijection f -> f:[a :\: b]: = f:[a]: :\: f:[b]:.
Proof.
  intros f a b H1.
Admitted.
