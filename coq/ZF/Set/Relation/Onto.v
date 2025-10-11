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
Require Import ZF.Set.Relation.Fun.
Require Import ZF.Set.Relation.FunctionOn.
Require Import ZF.Set.Relation.Image.
Require Import ZF.Set.Relation.InvImage.
Require Import ZF.Set.Relation.OneToOne.
Require Import ZF.Set.Relation.Range.
Require Import ZF.Set.Relation.Restrict.

(* f is a surjective function from a to b.                                      *)
Definition Onto (f a b:U) : Prop := FunctionOn f a /\ range f = b.


Proposition IsFun : forall (f a b:U), Onto f a b -> Fun f a b.
Proof.
  intros f a b [H1 H2]. split. 1: apply H1. rewrite H2. apply Incl.Refl.
Qed.

Proposition IsOneToOne : forall (f a b:U),
  Onto f a b                                            ->
  (forall x y, x :< a -> y :< a -> f!x = f!y -> x = y)  ->
  OneToOne f.
Proof.
  intros f a b H1. apply FunctionOn.IsOneToOne, H1.
Qed.

(* Two surjections with the same domains and which coincide pointwise are equal.*)
Proposition EqualCharac : forall (f a b g c d:U),
  Onto f a b                      ->
  Onto g c d                      ->
  a = c                           ->
  (forall x, x :< a -> f!x = g!x) ->
  f = g.
Proof.
  intros f a b g c d [H1 _] [H2 _]. apply FunctionOn.EqualCharac; assumption.
Qed.

(* The direct image of the domain is the range.                                 *)
Proposition ImageOfDomain : forall (f a b:U),
  Onto f a b -> f:[a]: =  b.
Proof.
  intros f a b H1. rewrite FunctionOn.ImageOfDomain; apply H1.
Qed.

(* A surjection f:a -> b is a subset of axb.                                    *)
Proposition IsIncl : forall (f a b:U),
  Onto f a b -> f :<=: a :x: b.
Proof.
  intros f a b H1. apply Fun.IsIncl, IsFun. assumption.
Qed.

(* The inverse image of the range is the domain.                                *)
Proposition InvImageOfRange : forall (f a b:U),
  Onto f a b -> f^:-1::[b]: = a.
Proof.
  intros f a b [H1 H2].
  rewrite <- H2. apply FunctionOn.InvImageOfRange. assumption.
Qed.

(* If f and g are surjections then so is the composition g.f.                   *)
Proposition Compose : forall (f g a b c:U),
  Onto f a b ->
  Onto g b c ->
  Onto (g :.: f) a c.
Proof.
  intros f g a b c [H1 H2] [H3 H4]. split.
  - apply FunctionOn.Compose with b; try assumption. subst. apply Incl.Refl.
  - rewrite Compose.RangeIsSame. 1: assumption.
    destruct H3 as [_ H3]. rewrite H2, H3. apply Incl.Refl.
Qed.

Proposition EvalCharac : forall (f a b x y:U),
  Onto f a b -> x :< a -> :(x,y): :< f <-> f!x = y.
Proof.
  intros f a b x y H1. apply FunctionOn.EvalCharac, H1.
Qed.

Proposition Satisfies : forall (f a b x:U),
  Onto f a b -> x :< a -> :(x,f!x): :< f.
Proof.
  intros f a b x H1. apply FunctionOn.Satisfies, H1.
Qed.

Proposition IsInRange : forall (f a b x:U),
  Onto f a b -> x :< a -> f!x :< b.
Proof.
  intros f a b x [H1 H2] H3. rewrite <- H2.
  apply FunctionOn.IsInRange with a; assumption.
Qed.

Proposition ImageCharac : forall (f a b c:U), Onto f a b ->
  forall y, y :< f:[c]: <-> exists x, x :< c /\ x :< a /\ f!x = y.
Proof.
  intros f a b c H1. apply FunctionOn.ImageCharac, H1.
Qed.

Proposition DomainOfCompose : forall (f g a b c:U),
  Onto f a b  ->
  Onto g b c  ->
  domain (g :.: f) =  a.
Proof.
  intros f g a b c [H1 H2] [H3 H4]. apply DoubleInclusion. split; intros x H5.
  - apply (FunctionOn.DomainOfCompose f g a b x H1 H3) in H5. apply H5.
  - apply (FunctionOn.DomainOfCompose f g a b x); try assumption.
    split. 1: assumption. apply IsInRange with a. 2: assumption. split; assumption.
Qed.

(* The value at x of g.f is the value at f!x of g when x in a.                  *)
Proposition ComposeEval : forall (f g a b c x:U),
  Onto f a b              ->
  Onto g b c              ->
  x :< a                  ->
  (g :.: f)!x = g!(f!x).
Proof.
  intros f g a b c x [H1 H2] [H3 H4] H5.
  apply (FunctionOn.ComposeEval f g a b); try assumption.
  apply IsInRange with a. 2: assumption. split; assumption.
Qed.

(* Characterisation of the range of F.                                          *)
Proposition RangeCharac : forall (f a b y:U),
  Onto f a b -> y :< b <-> exists x, x :< a /\ f!x = y.
Proof.
  intros f a b y [H1 H2]. subst. apply FunctionOn.RangeCharac. assumption.
Qed.

(* If the domain of f is not empty, then neither is the range.                  *)
Proposition RangeIsNotEmpty : forall (f a b:U),
  Onto f a b -> a <> :0: -> b <> :0:.
Proof.
  intros f a b [H1 H2]. subst. apply FunctionOn.RangeIsNotEmpty. assumption.
Qed.

Proposition IsRestrict : forall (f a b:U),
  Onto f a b -> f = f :|: a.
Proof.
  intros f a b H1. apply FunctionOn.IsRestrict, H1.
Qed.

Proposition Restrict : forall (f a b c:U),
  Onto f a b -> c :<=: a -> Onto (f:|:c) c f:[c]:.
Proof.
  intros f a b c [H1 H2] H3. split.
  - apply FunctionOn.Restrict with a; assumption.
  - apply Restrict.RangeOf.
Qed.

Proposition RestrictEqual : forall (f a b g c d e:U),
  Onto f a b                      ->
  Onto g c d                      ->
  e :<=: a                        ->
  e :<=: c                        ->
  (forall x, x :< e -> f!x = g!x) ->
  f:|:e =  g:|:e.
Proof.
  intros f a b g c d e [H1 _] [H2 _]. apply FunctionOn.RestrictEqual; assumption.
Qed.

