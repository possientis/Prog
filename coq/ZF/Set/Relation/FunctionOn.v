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
Require Import ZF.Set.Relation.Function.
Require Import ZF.Set.Relation.Image.
Require Import ZF.Set.Relation.InvImage.
Require Import ZF.Set.Relation.OneToOne.
Require Import ZF.Set.Relation.Range.
Require Import ZF.Set.Relation.Restrict.

(* f is a function defined on a.                                                *)
Definition FunctionOn (f a:U) : Prop := Function f /\ domain f = a.

Proposition IsOneToOne : forall (f a:U),
  FunctionOn f a                                        ->
  (forall x y, x :< a -> y :< a -> f!x = f!y -> x = y)  ->
  OneToOne f.
Proof.
  intros f a H1 H2. apply Function.IsOneToOne. 1: apply H1.
  intros x y H3 H4. destruct H1 as [_ H1].
  rewrite H1 in H3. rewrite H1 in H4. apply H2; assumption.
Qed.

(* Two functions with the same domains and which coincide pointwise are equal.  *)
Proposition EqualCharac : forall (f g a b:U),
  FunctionOn f a                   ->
  FunctionOn g b                   ->
  a = b                            ->
  (forall x, x :< a -> f!x = g!x)  ->
  f = g.
Proof.
  intros f g a b [H1 H2] [H3 H4] H5 H6. subst.
  apply Function.EqualCharac; assumption.
Qed.

(* The direct image of the domain is the range.                                 *)
Proposition ImageOfDomain : forall (f a:U),
  FunctionOn f a -> f:[a]: = range f.
Proof.
  intros f a [H1 H2]. rewrite <- H2. apply Range.ImageOfDomain.
Qed.

(* If f is a function defined on a, then it is a subset of a x f[a].            *)
Proposition IsIncl : forall (f a:U),
  FunctionOn f a -> f :<=: a :x: f:[a]:.
Proof.
  intros f a [H1 H2]. rewrite <- H2. apply Function.IsIncl. assumption.
Qed.

(* The inverse image of the range is the domain.                                *)
Proposition InvImageOfRange : forall (f a:U),
  FunctionOn f a -> f^:-1::[range f]: = a.
Proof.
  intros f a [H1 H2]. rewrite <- H2. apply InvImage.OfRange.
Qed.

(* If f defined on a, g defined on b and range f <= b, then g.f defined on a.   *)
Proposition Compose : forall (f g a b:U),
  FunctionOn f a ->
  FunctionOn g b ->
  range f :<=: b ->
  FunctionOn (g :.: f) a.
Proof.
  intros f g a b [H1 H2] [H3 H4] H5. split.
  - apply Function.Compose; assumption.
  - rewrite <- H2. apply Compose.DomainIsSame. rewrite H4. assumption.
Qed.

(* Characterization of the value at x of a function defined on a when x in a.   *)
Proposition EvalCharac : forall (f a x y:U),
  FunctionOn f a -> x :< a -> :(x,y): :< f <-> f!x = y.
Proof.
  intros f a x y [H1 H2] H3. subst. apply Function.EvalCharac; assumption.
Qed.

(* The ordered pair (x,f!x) lies in the set f when x in a.                      *)
Proposition Satisfies : forall (f a x:U),
  FunctionOn f a -> x :< a -> :(x,f!x): :< f.
Proof.
  intros F A a [H1 H2] H3. subst. apply Function.Satisfies; assumption.
Qed.

(* The value at x of a function defined on a lies in the range when x im a.     *)
Proposition IsInRange : forall (f a x:U),
  FunctionOn f a -> x :< a -> f!x :< range f.
Proof.
  intros F A a [H1 H2] H3. subst. apply Function.IsInRange; assumption.
Qed.

Proposition ImageCharac : forall (f a b:U), FunctionOn f a ->
  forall y, y :< f:[b]: <-> exists x, x :< b /\ x :< a /\ f!x = y.
Proof.
  intros f a b [H1 H2]. subst. apply Function.ImageCharac. assumption.
Qed.

(* Characterization of the domain of g.f.                                       *)
Proposition DomainOfCompose : forall (f g a b x:U),
  FunctionOn f a ->
  FunctionOn g b ->
  x :< domain (g :.: f) <-> x :< a /\ f!x :< b.
Proof.
  intros f g a b x [H1 H2] [H3 H4]. subst.
  apply Function.DomainOfCompose. assumption.
Qed.

(* The value at x of g.f is the value at f!x of g when x in a and f!x in b.     *)
Proposition ComposeEval : forall (f g a b x:U),
  FunctionOn f a ->
  FunctionOn g b ->
  x   :< a       ->
  f!x :< b       ->
  (g :.: f)!x = g!(f!x).
Proof.
  intros f g a b x [H1 H2] [H3 H4]. subst. apply Function.ComposeEval; assumption.
Qed.

(* Characterisation of the range of f.                                          *)
Proposition RangeCharac : forall (f a y:U),
  FunctionOn f a -> y :< range f <-> exists x, x :< a /\ f!x = y.
Proof.
  intros f a y [H1 H2]. subst. apply Function.RangeCharac. assumption.
Qed.

(* If the domain of f is not empty, then neither is the range.                  *)
Proposition RangeIsNotEmpty : forall (f a:U),
  FunctionOn f a -> a <> :0: -> range f <> :0:.
Proof.
  intros f a [H1 H2]. subst. apply Function.RangeIsNotEmpty.
Qed.

Proposition IsRestrict : forall (f a:U),
  FunctionOn f a -> f = f :|: a.
Proof.
  intros f a [H1 H2]. subst. apply Function.IsRestrict. assumption.
Qed.

Proposition Restrict : forall (f a b:U),
  FunctionOn f a ->  b :<=: a -> FunctionOn (f:|:b) b.
Proof.
  intros f a b [H1 H2] H3. split.
  - apply Function.Restrict. assumption.
  - rewrite Restrict.DomainOf, H2. apply Inter2.WhenInclL. assumption.
Qed.

Proposition RestrictEqual : forall (f g a b c:U),
  FunctionOn f a                  ->
  FunctionOn g b                  ->
  c :<=: a                        ->
  c :<=: b                        ->
  (forall x, x :< c -> f!x = g!x) ->
  f:|:c = g:|:c.
Proof.
  intros f g a b c [H1 H2] [H3 H4] H5 H6.
  apply Function.RestrictEqual; try assumption.
  - rewrite H2. assumption.
  - rewrite H4. assumption.
Qed.

(* A function is a function defined on its domain.                              *)
Proposition FunctionIsFunctionOn : forall (f:U),
  Function f -> FunctionOn f (domain f).
Proof.
  intros f H1. split. 1: assumption. reflexivity.
Qed.

