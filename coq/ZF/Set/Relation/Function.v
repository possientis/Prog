Require Import ZF.Class.Equiv.
Require Import ZF.Class.Relation.Function.
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
Require Import ZF.Set.Relation.Functional.
Require Import ZF.Set.Relation.Image.
Require Import ZF.Set.Relation.InvImage.
Require Import ZF.Set.Relation.OneToOne.
Require Import ZF.Set.Relation.Range.
Require Import ZF.Set.Relation.Relation.
Require Import ZF.Set.Relation.Restrict.
Require Import ZF.Set.Single.

Module CRF := ZF.Class.Relation.Function.
Module SRI := ZF.Set.Relation.InvImage.

(* A set is a function iff it is a relation and it is functional.               *)
Definition Function (f:U) : Prop := Relation f /\ Functional f.

(* If the set is a function, then so is the class.                              *)
Proposition ToClass : forall (f:U),
  Function f -> CRF.Function (toClass f).
Proof.
  intros f H1. assumption.
Qed.

(* If the class is a function, then so is the set.                              *)
Proposition FromClass : forall (f:U),
  CRF.Function (toClass f) -> Function f.
Proof.
  intros f H1. assumption.
Qed.

(* A function that is injective on its domain is one-to-one.                    *)
Proposition IsOneToOne : forall (f:U),
  Function f                                                          ->
  (forall x y, x :< domain f -> y :< domain f -> f!x = f!y -> x = y)  ->
  OneToOne f.
Proof.
  intros f H1. apply OneToOne.WhenFunctional, H1.
Qed.

(* Two functions with the same domains which coincide pointwise are equal.      *)
Proposition Equal : forall (f g:U),
  Function f                              ->
  Function g                              ->
  domain f = domain g                     ->
  (forall x, x :< domain f -> f!x = g!x)  ->
  f = g.
Proof.
  intros f g [H1 H2] [H3 H4] H5 H6. apply Incl.Double. split; intros x H7.
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
  apply SRI.OfRange.
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

(* For a function f and x in its domain, (x,y) lies in f iff f!x = y.           *)
Proposition Eval' : forall (f x y:U),
  Function f -> x :< domain f -> :(x,y): :< f <-> f!x = y.
Proof.
  intros f x y H1. apply Eval.Charac, H1.
Qed.

(* If (x,y) belongs to a function f then f!x = y.                               *)
Proposition Eval : forall (f x y:U),
  Function f -> :(x,y): :< f -> f!x = y.
Proof.
  intros f x y H1 H2. apply Eval'; try assumption.
  apply Domain.Charac. exists y. assumption.
Qed.

(* For a function f and x in its domain, the pair (x,f!x) lies in f.            *)
Proposition Satisfies : forall (f x:U),
  Function f -> x :< domain f -> :(x,f!x): :< f.
Proof.
  intros f x H1. apply Eval.Satisfies, H1.
Qed.

(* For a function f and x in its domain, the value f!x lies in the range.       *)
Proposition IsInRange : forall (f x:U),
  Function f -> x :< domain f -> f!x :< range f.
Proof.
  intros f x H1. apply Eval.IsInRange, H1.
Qed.

(* y lies in f[a] iff y = f!x for some x in both a and the domain of f.         *)
Proposition ImageCharac : forall (f a: U), Function f ->
  forall y, y :< f:[a]: <-> exists x, x :< a /\ x :< domain f /\ f!x = y.
Proof.
  intros f a H1. apply Eval.ImageCharac, H1.
Qed.

(* x is in the domain of g.f iff x is in the domain of f and f(x) in that of g. *)
Proposition DomainOfCompose : forall (f g x:U),
  Function f -> x :< domain (g :.: f) <-> x :< domain f /\ f!x :< domain g.
Proof.
  intros F G x H1. apply Compose.FunctionalDomainCharac, H1.
Qed.

(* (g.f)(x) = g(f(x)) when x is in the domain of f and f(x) is in that of g.    *)
Proposition ComposeEval : forall (f g x:U),
  Function f      ->
  Function g      ->
  x :< domain f   ->
  f!x :< domain g ->
  (g :.: f)!x = g!(f!x).
Proof.
  intros f g x [_ H1] [_ H2]. apply Compose.Eval; assumption.
Qed.

(* y lies in the range of a function f iff y = f!x for some x in the domain.    *)
Proposition RangeCharac : forall (f y:U),
  Function f -> y :< range f <-> exists x, x :< domain f /\ f!x = y.
Proof.
  intros f y H1. split; intros H2.
  - apply Range.Charac in H2. destruct H2 as [x H2]. exists x. split.
    + apply Domain.Charac. exists y. assumption.
    + apply Eval'; try assumption. apply Domain.Charac.
      exists y. assumption.
  - destruct H2 as [x [H2 H3]]. apply Range.Charac. exists x.
    apply Eval'; assumption.
Qed.

(* If the domain of f is not empty, then neither is the range.                  *)
Proposition RangeIsNotEmpty : forall (f:U),
  domain f <> :0: -> range f <> :0:.
Proof.
  apply Range.IsNotEmpty.
Qed.

(* A function equals its own restriction to its domain.                         *)
Proposition IsRestrict : forall (f:U),
  Function f -> f = f :|: domain f.
Proof.
  intros f H1. apply Restrict.RelationCharac, H1.
Qed.

(* The restriction of a function to any set is again a function.                *)
Proposition Restrict : forall (f a:U),
  Function f  -> Function (f:|:a).
Proof.
  intros f a H1. split.
  - apply Restrict.IsRelation.
  - apply Restrict.IsFunctional, H1.
Qed.

(* Functions agreeing on a subset a of the domains have equal restrictions to a *)
Proposition RestrictEqual : forall (f g a:U),
  Function f                      ->
  Function g                      ->
  a :<=: domain f                 ->
  a :<=: domain g                 ->
  (forall x, x :< a -> f!x = g!x) ->
  f:|:a = g:|:a.
Proof.
  intros f g a H1 H2 H3 H4 H5.
  assert (domain (f:|:a) = a) as H6. {
    rewrite Restrict.DomainOf. apply Inter2.WhenInclL. assumption. }
  assert (domain (g:|:a) = a) as H7. {
    rewrite Restrict.DomainOf. apply Inter2.WhenInclL. assumption. }
  apply Equal.
  - apply Restrict. assumption.
  - apply Restrict. assumption.
  - rewrite H6, H7. reflexivity.
  - intros x H8. rewrite H6 in H8.
    rewrite Restrict.Eval, Restrict.Eval; try assumption.
    + apply H5. assumption.
    + apply H2.
    + apply H1.
Qed.

(* The empty set is a function.                                                 *)
Proposition WhenEmpty : forall (f:U),
  f = :0: -> Function f.
Proof.
  intros f H1. split.
  - apply Relation.WhenEmpty. assumption.
  - apply Functional.WhenEmpty. assumption.
Qed.

(* A singleton set containing a single ordered pair is a function.              *)
Proposition WhenSingle : forall (x y f:U),
  f = :{ :(x,y): }: -> Function f.
Proof.
  intros x y f H1. split.
  - apply Relation.WhenSingle with x y. assumption.
  - apply Functional.WhenSingle with x y. assumption.
Qed.

