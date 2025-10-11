Require Import ZF.Set.Core.
Require Import ZF.Set.Diff.
Require Import ZF.Set.Empty.
Require Import ZF.Set.Incl.
Require Import ZF.Set.Inter2.
Require Import ZF.Set.OrdPair.
Require Import ZF.Set.Prod.
Require Import ZF.Set.Relation.BijectionOn.
Require Import ZF.Set.Relation.Compose.
Require Import ZF.Set.Relation.Converse.
Require Import ZF.Set.Relation.Domain.
Require Import ZF.Set.Relation.Eval.
Require Import ZF.Set.Relation.Fun.
Require Import ZF.Set.Relation.FunctionOn.
Require Import ZF.Set.Relation.Image.
Require Import ZF.Set.Relation.Inj.
Require Import ZF.Set.Relation.Onto.
Require Import ZF.Set.Relation.Range.
Require Import ZF.Set.Relation.Restrict.

(* f is a bijection from a to b.                                                *)
Definition Bij (f a b:U) : Prop := BijectionOn f a /\ range f = b.

Proposition IsFun : forall (f a b:U),
  Bij f a b -> Fun f a b.
Proof.
  intros f a b [H1 H2]. apply BijectionOn.IsFunctionOn in H1.
  split. 1: assumption. subst. apply Incl.Refl.
Qed.

Proposition IsInj : forall (f a b:U),
  Bij f a b -> Inj f a b.
Proof.
  intros f a b [H1 H2]. split. 1: apply H1. subst. apply Incl.Refl.
Qed.

Proposition IsOnto : forall (f a b:U),
  Bij f a b -> Onto f a b.
Proof.
  intros f a b H1. split. 2: apply H1. apply BijectionOn.IsFunctionOn, H1.
Qed.

(* Two bijections with the same domains and which coincide pointwise are equal. *)
Proposition EqualCharac : forall (f a b g c d:U),
  Bij f a b                       ->
  Bij g c d                       ->
  a = c                           ->
  (forall x, x :< a -> f!x = g!x) ->
  f = g.
Proof.
  intros f a b g c d [H1 _] [H2i _]. apply BijectionOn.EqualCharac; assumption.
Qed.

Proposition ImageOfDomain : forall (f a b:U),
  Bij f a b -> f:[a]: = b.
Proof.
  intros f a b [H1 H2]. subst. apply BijectionOn.ImageOfDomain. assumption.
Qed.

(* A bijection f:a -> b is a subset of axb.                                     *)
Proposition IsIncl : forall (f a b:U),
  Bij f a b -> f :<=: a :x: b.
Proof.
  intros f a b H1. apply Fun.IsIncl, IsFun. assumption.
Qed.

Proposition InvImageOfRange : forall (f a b:U),
  Bij f a b -> f^:-1::[b]: = a.
Proof.
  intros f a b [H1 H2]. subst. apply BijectionOn.InvImageOfRange. assumption.
Qed.

Proposition Compose : forall (f g a b c:U),
  Bij f a b -> Bij g b c -> Bij (g :.: f) a c.
Proof.
  intros f g a b c [H1 H2] [H3 H4]. split.
  - apply BijectionOn.Compose with b; try assumption. subst. apply Incl.Refl.
  - subst. apply Compose.RangeIsSame. destruct H3 as [_ H3].
    rewrite H3. apply Incl.Refl.
Qed.

Proposition EvalCharac : forall (f a b x y:U),
  Bij f a b-> x :< a -> :(x,y): :< f <-> f!x = y.
Proof.
  intros f a b x y H1. apply IsFun in H1. apply Fun.EvalCharac with b. assumption.
Qed.

Proposition Satisfies : forall (f a b x:U),
  Bij f a b -> x :< a -> :(x,f!x): :< f.
Proof.
  intros f a b x H1. apply IsFun in H1. apply Fun.Satisfies with b. assumption.
Qed.

Proposition IsInRange : forall (f a b x:U),
  Bij f a b -> x :< a -> f!x :< b.
Proof.
  intros f a b x H1. apply IsFun in H1. apply Fun.IsInRange. assumption.
Qed.

Proposition ImageCharac : forall (f a b c:U), Bij f a b ->
  forall y, y :< f:[c]: <-> exists x, x :< c /\ x :< a /\ f!x = y.
Proof.
  intros f a b c H1. apply BijectionOn.ImageCharac, H1.
Qed.

Proposition DomainOfCompose : forall (f g a b c:U),
  Bij f a b             ->
  Bij g b c             ->
  domain (g :.: f) = a.
Proof.
  intros f g a b c H1 H2.
  apply Fun.DomainOfCompose with b c; apply IsFun; assumption.
Qed.

Proposition ComposeEval : forall (f g a b c x:U),
  Bij f a b               ->
  Bij g b c               ->
  x :< a                  ->
  (g :.: f)!x = g!(f!x).
Proof.
  intros f g a b c x H1 H2.
  apply Fun.ComposeEval with b c; apply IsFun; assumption.
Qed.

(* Characterisation of the range of f.                                          *)
Proposition RangeCharac : forall (f a b y:U),
  Bij f a b -> y :< b <-> exists x, x :< a /\ f!x = y.
Proof.
  intros f a b y [H1 H2]. subst. apply BijectionOn.RangeCharac. assumption.
Qed.

Proposition RangeIsNotEmpty : forall (f a b:U),
  Bij f a b -> a <> :0: -> b <> :0:.
Proof.
  intros f a b H1. apply Onto.RangeIsNotEmpty with f, IsOnto. assumption.
Qed.

Proposition IsRestrict : forall (f a b:U),
  Bij f a b -> f = f :|: a.
Proof.
  intros f a b H1. apply BijectionOn.IsRestrict, H1.
Qed.

Proposition Restrict : forall (f a b c:U),
  Bij f a b -> c :<=: a -> Bij (f:|:c) c f:[c]:.
Proof.
  intros f a b c [H1 H2] H3. split.
  - apply BijectionOn.Restrict with a; assumption.
  - apply Restrict.RangeOf.
Qed.

Proposition RestrictEqual : forall (f a b g c d e:U),
  Bij f a b                       ->
  Bij g c d                       ->
  e :<=: a                        ->
  e :<=: c                        ->
  (forall x, x :< e -> f!x = g!x) ->
  f:|:e = g:|:e.
Proof.
  intros f a b g c d e [H1 _] [H2 _]. apply BijectionOn.RestrictEqual; assumption.
Qed.

Proposition Converse : forall (f a b:U),
  Bij f a b -> Bij f^:-1: b a.
Proof.
  intros f a b [H1 H2]. split.
  - apply BijectionOn.Converse with a; assumption.
  - destruct H1 as [_ H1]. subst. apply Converse.Range.
Qed.

Proposition ConverseEvalIsInDomain : forall (f a b y:U),
  Bij f a b -> y :< b -> f^:-1:!y :< a.
Proof.
  intros f a b y H1 H2. apply IsInRange with b. 2: assumption.
  apply Converse. assumption.
Qed.

Proposition ConverseEvalOfEval : forall (f a b x:U),
  Bij f a b -> x :< a -> f^:-1:!(f!x) = x.
Proof.
  intros f a b x H1. apply BijectionOn.ConverseEvalOfEval, H1.
Qed.

Proposition EvalOfConverseEval : forall (f a b y:U),
  Bij f a b -> y :< b -> f!(f^:-1:!y) = y.
Proof.
  intros f a b y [H1 H2] H3. subst.
  apply BijectionOn.EvalOfConverseEval with a; assumption.
Qed.

Proposition InvImageOfImage : forall (f a b c:U),
  Bij f a b -> c :<=: a -> f^:-1::[ f:[c]: ]: = c.
Proof.
  intros f a b c [H1 H2] H3. apply BijectionOn.InvImageOfImage with a; assumption.
Qed.

Proposition ImageOfInvImage : forall (f a b c:U),
  Bij f a b -> c :<=: b -> f:[ f^:-1::[c]: ]: = c.
Proof.
  intros f a b c [H1 H2] H3.
  subst. apply BijectionOn.ImageOfInvImage with a; assumption.
Qed.

Proposition EvalInjective : forall (f a b x y:U),
  Bij f a b -> x :< a -> y :< a -> f!x = f!y -> x = y.
Proof.
  intros f a b x y H1. apply BijectionOn.EvalInjective, H1.
Qed.

Proposition EvalInImage : forall (f a b c x:U),
  Bij f a b -> x :< a -> f!x :< f:[c]: <-> x :< c.
Proof.
  intros f a b c x H1. apply BijectionOn.EvalInImage, H1.
Qed.

Proposition Inter2Image : forall (f a b c d:U),
  Bij f a b -> f:[c :/\: d]: = f:[c]: :/\: f:[d]:.
Proof.
  intros f a b c d H1. apply BijectionOn.Inter2Image with a, H1.
Qed.

Proposition DiffImage : forall (f a b c d:U),
  Bij f a b -> f:[c :\: d]: = f:[c]: :\: f:[d]:.
Proof.
  intros f a b c d H1. apply BijectionOn.DiffImage with a, H1.
Qed.

