Require Import ZF.Set.Core.
Require Import ZF.Set.Diff.
Require Import ZF.Set.Empty.
Require Import ZF.Set.Incl.
Require Import ZF.Set.Inter2.
Require Import ZF.Set.OrdPair.
Require Import ZF.Set.Prod.
Require Import ZF.Set.Relation.Bijection.
Require Import ZF.Set.Relation.Compose.
Require Import ZF.Set.Relation.Converse.
Require Import ZF.Set.Relation.Domain.
Require Import ZF.Set.Relation.Eval.
Require Import ZF.Set.Relation.FunctionOn.
Require Import ZF.Set.Relation.Image.
Require Import ZF.Set.Relation.InvImage.
Require Import ZF.Set.Relation.Range.
Require Import ZF.Set.Relation.Restrict.

(* f is a bijection defined on a.                                               *)
Definition BijectionOn (f a:U) : Prop := Bijection f /\ domain f = a.


(* A bijection defined on a is a function defined on a.                         *)
Proposition IsFunctionOn : forall (f a:U),
  BijectionOn f a -> FunctionOn f a.
Proof.
  intros f a [H1 H2]. subst.
  apply FunctionOn.FunctionIsFunctionOn, Bijection.IsFunction. assumption.
Qed.

(* Two bijections with the same domains and which coincide pointwise are equal. *)
Proposition EqualCharac : forall (f g a b:U),
  BijectionOn f a                  ->
  BijectionOn g b                  ->
  a = b                            ->
  (forall x, x :< a -> f!x = g!x)  ->
  f = g.
Proof.
  intros f g a b H1 H2.
  apply FunctionOn.EqualCharac; apply IsFunctionOn; assumption.
Qed.

Proposition ImageOfDomain : forall (f a:U),
  BijectionOn f a -> f:[a]: = range f.
Proof.
  intros f a H1. apply FunctionOn.ImageOfDomain, IsFunctionOn. assumption.
Qed.

Proposition IsIncl : forall (f a:U),
  BijectionOn f a -> f :<=: a :x: f:[a]:.
Proof.
  intros f a H1. apply FunctionOn.IsIncl, IsFunctionOn. assumption.
Qed.

Proposition InvImageOfRange : forall (f a:U),
  BijectionOn f a -> f^:-1::[range f]: = a.
Proof.
  intros f a H1. apply FunctionOn.InvImageOfRange, IsFunctionOn. assumption.
Qed.

Proposition Compose : forall (f g a b:U),
  BijectionOn f a ->
  BijectionOn g b ->
  range f :<=: b   ->
  BijectionOn (g :.: f) a.
Proof.
  intros f g a b [H1 H2] [H3 H4] H5. subst. split.
  - apply Bijection.Compose; assumption.
  - apply Compose.DomainIsSame. assumption.
Qed.

Proposition EvalCharac : forall (f a x y:U),
  BijectionOn f a -> x :< a -> :(x,y): :< f <-> f!x = y.
Proof.
  intros f a x y H1. apply FunctionOn.EvalCharac, IsFunctionOn. assumption.
Qed.

Proposition Satisfies : forall (f a x:U),
  BijectionOn f a -> x :< a -> :(x,f!x): :< f.
Proof.
  intros f a x H1. apply FunctionOn.Satisfies, IsFunctionOn. assumption.
Qed.

Proposition IsInRange : forall (f a x:U),
  BijectionOn f a -> x :< a -> f!x :< range f.
Proof.
  intros f a x H1. apply FunctionOn.IsInRange, IsFunctionOn. assumption.
Qed.

Proposition ImageCharac : forall (f a b:U), BijectionOn f a ->
  forall y, y :< f:[b]: <-> exists x, x :< b /\ x :< a /\ f!x = y.
Proof.
  intros f a b H1. apply FunctionOn.ImageCharac, IsFunctionOn. assumption.
Qed.

Proposition DomainOfCompose : forall (f g a b x:U),
  BijectionOn f a ->
  BijectionOn g b ->
  x :< domain (g :.: f) <-> x :< a /\ f!x :< b.
Proof.
  intros f g a b x H1 H2.
  apply FunctionOn.DomainOfCompose; apply IsFunctionOn; assumption.
Qed.

Proposition ComposeEval : forall (f g a b x:U),
  BijectionOn f a ->
  BijectionOn g b ->
  x   :< a        ->
  f!x :< b        ->
  (g :.: f)!x = g!(f!x).
Proof.
  intros f g a b x H1 H2.
  apply FunctionOn.ComposeEval; apply IsFunctionOn; assumption.
Qed.

Proposition RangeCharac : forall (f a y:U),
  BijectionOn f a -> y :< range f <-> exists x, x :< a /\ f!x = y.
Proof.
  intros f a y H1. apply FunctionOn.RangeCharac, IsFunctionOn. assumption.
Qed.

Proposition RangeIsNotEmpty : forall (f a:U),
  BijectionOn f a -> a <> :0: -> range f <> :0:.
Proof.
  intros f a H1. apply FunctionOn.RangeIsNotEmpty, IsFunctionOn. assumption.
Qed.

Proposition IsRestrict : forall (f a:U),
  BijectionOn f a -> f =  f:|:a.
Proof.
  intros f a H1. apply FunctionOn.IsRestrict, IsFunctionOn. assumption.
Qed.

Proposition Restrict : forall (f a b:U),
  BijectionOn f a -> BijectionOn (f:|:b) (a:/\:b).
Proof.
  intros f a b [H1 H2]. split.
  - apply Bijection.Restrict. assumption.
  - rewrite Restrict.DomainOf, H2. apply Inter2.Comm.
Qed.

Proposition RestrictEqual : forall (f g a b c:U),
  BijectionOn f a                 ->
  BijectionOn g b                 ->
  c :<=: a                        ->
  c :<=: b                        ->
  (forall x, x :< c -> f!x = g!x) ->
  f:|:c = g:|:c.
Proof.
  intros f g a b c [H1 H2] [H3 H4] H5 H6.
  apply Bijection.RestrictEqual; try assumption.
  - rewrite H2. assumption.
  - rewrite H4. assumption.
Qed.

Proposition Converse : forall (f a b:U),
  BijectionOn f a -> range f = b -> BijectionOn f^:-1: b.
Proof.
  intros f a b [H1 H2] H3. subst. split.
  - apply Bijection.Converse. assumption.
  - apply Converse.Domain.
Qed.

Proposition ConverseEvalIsInDomain : forall (f a y:U),
  BijectionOn f a -> y :< range f -> f^:-1:!y :< a.
Proof.
  intros f a y [H1 H2] H3. subst.
  apply Bijection.ConverseEvalIsInDomain; assumption.
Qed.

Proposition ConverseEvalOfEval : forall (f a x:U),
  BijectionOn f a -> x :< a -> f^:-1:!(f!x) = x.
Proof.
  intros f a x [H1 H2] H3. subst. apply Bijection.ConverseEvalOfEval; assumption.
Qed.

Proposition EvalOfConverseEval : forall (f a y:U),
  BijectionOn f a -> y :< range f -> f!(f^:-1:!y) = y.
Proof.
  intros f a y [H1 H2]. apply Bijection.EvalOfConverseEval. assumption.
Qed.

Proposition InvImageOfImage : forall (f a b:U),
  BijectionOn f a -> b :<=: a -> f^:-1::[ f:[b]: ]: = b.
Proof.
  intros f a b [H1 H2] H3. subst. apply Bijection.InvImageOfImage; assumption.
Qed.

Proposition ImageOfInvImage : forall (f a b:U),
  BijectionOn f a -> b :<=: range f -> f:[ f^:-1::[b]: ]: = b.
Proof.
  intros f a b H1. apply Bijection.ImageOfInvImage, H1.
Qed.

Proposition EvalInjective : forall (f a x y:U),
  BijectionOn f a -> x :< a -> y :< a-> f!x = f!y -> x = y.
Proof.
  intros F A x y [H1 H2] H3 H4. subst. apply Bijection.EvalInjective; assumption.
Qed.

Proposition EvalInImage : forall (f a b x:U),
  BijectionOn f a -> x :< a -> f!x :< f:[b]:  <-> x :< b.
Proof.
  intros f a b x [H1 H2] H3. subst. apply Bijection.EvalInImage; assumption.
Qed.

(* A bijection is a bijection defined on its domain.                            *)
Proposition BijectionIsBijectionOn : forall (f:U),
  Bijection f -> BijectionOn f (domain f).
Proof.
  intros f H1. split. 1: assumption. reflexivity.
Qed.

Proposition Inter2Image : forall (f a b c:U),
  BijectionOn f a -> f:[b :/\: c]: = f:[b]: :/\: f:[c]:.
Proof.
  intros f a b c H1. apply Bijection.Inter2Image, H1.
Qed.

Proposition DiffImage : forall (f a b c:U),
  BijectionOn f a -> f:[b :\: c]: = f:[b]: :\: f:[c]:.
Proof.
  intros f a b c H1. apply Bijection.DiffImage, H1.
Qed.

