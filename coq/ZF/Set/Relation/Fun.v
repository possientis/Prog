Require Import ZF.Set.Core.
Require Import ZF.Set.Empty.
Require Import ZF.Set.Incl.
Require Import ZF.Set.Inter2.
Require Import ZF.Set.OrdPair.
Require Import ZF.Set.Prod.
Require Import ZF.Set.Relation.Compose.
Require Import ZF.Set.Relation.Converse.
Require Import ZF.Set.Relation.Domain.
Require Import ZF.Set.Relation.Eval.
Require Import ZF.Set.Relation.FunctionOn.
Require Import ZF.Set.Relation.Image.
Require Import ZF.Set.Relation.Range.
Require Import ZF.Set.Relation.Restrict.

Require Import ZF.Notation.Fun.
Export ZF.Notation.Fun.

(* f is a function from a to b.                                                 *)
Definition Fun (f a b:U) : Prop := FunctionOn f a /\ range f :<=: b.

(* Notation "f :: a :-> b" := (Fun f a b)                                       *)
Global Instance SetFun : Notation.Fun.Fun U U := { IsFun := Fun }.

(* Two functions with the same domains and which coincide pointwise are equal.  *)
Proposition EqualCharac : forall (f a b g c d:U),
  f :: a :-> b                    ->
  g :: c :-> d                    ->
  a = c                           ->
  (forall x, x :< a -> f!x = g!x) ->
  f = g.
Proof.
  intros f a b g c d [H1 _] [H2 _]. apply FunctionOn.EqualCharac; assumption.
Qed.

(* The direct image of the domain is the range.                                 *)
Proposition ImageOfDomain : forall (f a b:U),
  f :: a :-> b -> f:[a]: = range f.
Proof.
  intros f a b [H1 _]. apply FunctionOn.ImageOfDomain. assumption.
Qed.

(* A function f:a -> b is a subset of axb.                                      *)
Proposition IsIncl : forall (f a b:U),
  f :: a :-> b -> f :<=: a :x: b.
Proof.
  intros f a b H1. apply ZF.Set.Incl.Tran with (a :x: f:[a]:).
  - apply FunctionOn.IsIncl, H1.
  - apply Prod.InclCompatR. rewrite (ImageOfDomain f a b).
    2: assumption. apply H1.
Qed.

(* The inverse image of the range is the domain.                                *)
Proposition InvImageOfRange : forall (f a b:U),
  f :: a :-> b -> f^:-1::[range f]: = a.
Proof.
  intros f a b H1. apply FunctionOn.InvImageOfRange, H1.
Qed.

(* If f:a -> b and g:b -> c then g.f : a -> c.                                  *)
Proposition Compose : forall (f g a b c:U),
  f :: a :-> b          ->
  g :: b :-> c          ->
  (g :.: f) :: a :-> c.
Proof.
  intros f g a b c [H1 H2] [H3 H4]. split.
  - apply FunctionOn.Compose with b; assumption.
  - apply ZF.Set.Incl.Tran with (range g). 2: assumption.
    apply Compose.RangeIsSmaller.
Qed.

(* Characterization of the value at x of a function defined on a when x in a.   *)
Proposition EvalCharac : forall (f a b x y:U),
  f :: a :-> b -> x :< a -> :(x,y): :< f <-> f!x = y.
Proof.
  intros f a b x y H1. apply FunctionOn.EvalCharac, H1.
Qed.

(* The ordered pair (x,f!x) lies in the set f when x in a.                      *)
Proposition Satisfies : forall (f a b x:U),
  f :: a :-> b -> x :< a -> :(x,f!x): :< f.
Proof.
  intros f a b x H1. apply FunctionOn.Satisfies, H1.
Qed.

(* The value at x of a function defined on a lies in b  when x im a.            *)
Proposition IsInRange : forall (f a b x:U),
  f :: a :-> b -> x :< a -> f!x :< b.
Proof.
  intros f a b x H1 H2. apply H1.
  apply FunctionOn.IsInRange with a. 2: assumption. apply H1.
Qed.

Proposition ImageCharac : forall (f a b c:U), f :: a :-> b ->
  forall y, y :< f:[c]: <-> exists x, x :< c /\ x :< a /\ f!x = y.
Proof.
  intros f a b c H1. apply FunctionOn.ImageCharac, H1.
Qed.

(* Characterization of the domain of g.f.                                       *)
Proposition DomainOfCompose : forall (f g a b c:U),
  f :: a :-> b  ->
  g :: b :-> c  ->
  domain (g :.: f) = a.
Proof.
  intros f g a b c [H1 H2] [H3 H4]. apply DoubleInclusion. split; intros x H5.
  - apply (FunctionOn.DomainOfCompose f g a b x H1 H3) in H5.
    destruct H5 as [H5 H6]. assumption.
  - apply (FunctionOn.DomainOfCompose f g a b x); try assumption.
    split. 1: assumption. apply IsInRange with a. 2: assumption.
    split; assumption.
Qed.

(* The value at x of g.f is the value at f!x of g when x in a.                  *)
Proposition ComposeEval : forall (f g a b c x:U),
  f :: a :-> b  ->
  g :: b :-> c  ->
  x :< a        ->
  (g :.: f)!x = g!(f!x).
Proof.
  intros f g a b c x [H1 H2] [H3 H4] H5.
  apply (FunctionOn.ComposeEval f g a b); try assumption.
  apply IsInRange with a. 2: assumption. split; assumption.
Qed.

(* Characterisation of the range of f.                                          *)
Proposition RangeCharac : forall (f a b y:U),
  f :: a :-> b -> y :< range f <-> exists x, x :< a /\ f!x = y.
Proof.
  intros f a b y H1. apply FunctionOn.RangeCharac, H1.
Qed.

(* If the domain of f is not empty, then neither is the range.                  *)
Proposition RangeIsNotEmpty : forall (f a b:U),
  f :: a :-> b -> a <> :0: -> range f <> :0:.
Proof.
  intros f a b H1. apply FunctionOn.RangeIsNotEmpty, H1.
Qed.

Proposition IsRestrict : forall (f a b:U),
  f :: a :-> b -> f = f :|: a.
Proof.
  intros f a b H1. apply FunctionOn.IsRestrict, H1.
Qed.

Proposition Restrict : forall (f a b c:U),
  f :: a :-> b -> (f:|:c) :: (a :/\: c) :-> b.
Proof.
  intros f a b c H1. split.
  - apply FunctionOn.Restrict, H1.
  - apply Incl.Tran with (range f).
    + apply Restrict.RangeIsIncl.
    + apply H1.
Qed.

Proposition RestrictEqual : forall (f a b g c d e:U),
  f :: a :-> b                    ->
  g :: c :-> d                    ->
  e :<=: a                        ->
  e :<=: c                        ->
  (forall x, x :< e -> f!x = g!x) ->
  f:|:e = g:|:e.
Proof.
  intros f a b g c d e [H1 H2] [H3 H4].
  apply FunctionOn.RestrictEqual; assumption. 
Qed.

