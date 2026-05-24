Require Import ZF.Class.Equiv.
Require Import ZF.Class.Relation.Fun.From.
Require Import ZF.Set.Core.
Require Import ZF.Set.Incl.
Require Import ZF.Set.OrdPair.
Require Import ZF.Set.Relation.Bij.
Require Import ZF.Set.Relation.Bijection.
Require Import ZF.Set.Relation.BijectionOn.
Require Import ZF.Set.Relation.Domain.
Require Import ZF.Set.Relation.Eval.
Require Import ZF.Set.Relation.Fun.
Require Import ZF.Set.Relation.Function.
Require Import ZF.Set.Relation.Functional.
Require Import ZF.Set.Relation.FunctionOn.
Require Import ZF.Set.Relation.Inj.
Require Import ZF.Set.Relation.OneToOne.
Require Import ZF.Set.Relation.Onto.
Require Import ZF.Set.Relation.Range.
Require Import ZF.Set.Relation.Relation.
Require Import ZF.Set.Relation.RestrictOfClass.

Require Import ZF.Notation.Eval.

Module CFF := ZF.Class.Relation.Fun.From.
Module SRR := ZF.Set.Relation.RestrictOfClass.


(* Given a set a and Coq expression f representing a function on sets, we aim   *)
(* to quickly define the associated function with domain a.                     *)
Definition from (a:U) (f:U -> U) : U := :[f]: :|: a.

(* x belongs to the function on a defined by f iff x = (y,f y) for some y in a. *)
Proposition Charac : forall (f:U -> U) (a x:U),
  x :< from a f <-> exists y, x = :(y,f y): /\ y :< a.
Proof.
  intros f a x. split; intros H1.
  - apply SRR.Charac in H1. 2: apply CFF.IsFunctional.
    destruct H1 as [y [z [H1 [H2 H3]]]].
    apply CFF.Charac2 in H3. subst. exists y. split. 2: assumption.
    reflexivity.
  - destruct H1 as [y [H1 H2]]. subst.
    apply SRR.Charac2Rev. 2: assumption.
    + apply CFF.IsFunctional.
    + apply CFF.Charac2. reflexivity.
Qed.

Proposition Charac2 : forall (f:U -> U) (a x y:U),
  :(x,y): :< from a f <-> x :< a /\ y = f x.
Proof.
  intros f a x y. split; intros H1.
  - apply Charac in H1. destruct H1 as [z [H1 H2]].
    apply OrdPair.Equal in H1. destruct H1 as [H1 H3]. subst.
    split. 1: assumption. reflexivity.
  - destruct H1 as [H1 H2]. subst.
    apply Charac. exists x. split. 2: assumption. reflexivity.
Qed.

(* For x in a, the pair (x,f(x)) belongs to the function on a defined by f.     *)
Proposition Satisfies : forall (f:U -> U) (a x:U),
  x :< a -> :(x,f x): :< from a f.
Proof.
  intros f a x H1. apply Charac2. split. 1: assumption. reflexivity.
Qed.

(* The domain of the function on a defined by f is a.                           *)
Proposition DomainOf : forall (f:U -> U) (a:U),
  domain (from a f) = a.
Proof.
  intros f a. apply Incl.Double. split; intros x H1.
  - apply Domain.Charac in H1. destruct H1 as [y H1].
    apply Charac2 in H1. apply H1.
  - apply Domain.Charac. exists (f x). apply Satisfies. assumption.
Qed.

(* The function on a defined by f is a relation.                                *)
Proposition IsRelation : forall (f:U -> U) (a:U), Relation (from a f).
Proof.
  intros f a x H1. apply Charac in H1. destruct H1 as [y [H1 H2]].
  exists y. exists (f y). assumption.
Qed.

(* The function on a defined by f is functional.                                *)
Proposition IsFunctional : forall (f:U -> U) (a:U), Functional (from a f).
Proof.
  intros f a x y1 y2 H1 H2.
  apply Charac2 in H1. apply Charac2 in H2.
  destruct H1 as [_ H1]. destruct H2 as [_ H2]. subst. reflexivity.
Qed.

(* The function on a defined by f is a function.                                *)
Proposition IsFunction : forall (f:U -> U) (a:U), Function (from a f).
Proof.
  intros f a. split.
  - apply IsRelation.
  - apply IsFunctional.
Qed.

(* The function on a defined by f is a function with domain a.                  *)
Proposition IsFunctionOn : forall (f:U -> U) (a:U), FunctionOn (from a f) a.
Proof.
  intros f a. split.
  - apply IsFunction.
  - apply DomainOf.
Qed.

(* For x in a, evaluation of the function on a defined by f at x equals f x.    *)
Proposition Eval : forall (f:U -> U) (a x:U),
  x :< a -> (from a f)!x = f x.
Proof.
  intros f a x H1. apply Eval.Charac.
  - apply IsFunctional.
  - rewrite DomainOf. assumption.
  - apply Satisfies. assumption.
Qed.

(* If the values lie in b, then the function defined by f maps a to b.          *)
Proposition IsFun : forall (f:U -> U) (a b:U),
  (forall x, x :< a -> f x :< b) -> Fun (from a f) a b.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros f a b H1. split. 1: apply IsFunctionOn.
  (* Every value in the range is one of the displayed values f(x).              *)
  intros y H2. apply Range.Charac in H2. destruct H2 as [x H2].
  apply Charac2 in H2. destruct H2 as [H2 H3]. rewrite H3.
  apply H1. assumption.
Qed.

(* If the expression is injective on a, the associated function is one-to-one.  *)
Proposition IsOneToOne : forall (f:U -> U) (a:U),
  (forall x y, x :< a -> y :< a -> f x = f y -> x = y) ->
  OneToOne (from a f).
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros f a H1. apply FunctionOn.IsOneToOne with a.
  - apply IsFunctionOn.
  - (* Equal values of the associated function are equal values of f.           *)
    intros x y H2 H3 H4. rewrite Eval in H4. 2: assumption.
    rewrite Eval in H4. 2: assumption. apply H1; assumption.
Qed.

(* If the expression is injective on a, the associated relation is a bijection. *)
Proposition IsBijection : forall (f:U -> U) (a:U),
  (forall x y, x :< a -> y :< a -> f x = f y -> x = y) ->
  Bijection (from a f).
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros f a H1. split.
  - apply IsRelation.
  - apply IsOneToOne. assumption.
Qed.

(* If the expression is injective on a, it is a bijection defined on a.         *)
Proposition IsBijectionOn : forall (f:U -> U) (a:U),
  (forall x y, x :< a -> y :< a -> f x = f y -> x = y) ->
  BijectionOn (from a f) a.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros f a H1. split.
  - apply IsBijection. assumption.
  - apply DomainOf.
Qed.

(* If the values lie in b and are injective on a, we get an injection a -> b.   *)
Proposition IsInj : forall (f:U -> U) (a b:U),
  (forall x, x :< a -> f x :< b)                          ->
  (forall x y, x :< a -> y :< a -> f x = f y -> x = y)    ->
  Inj (from a f) a b.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros f a b H1 H2. split.
  - apply IsBijectionOn. assumption.
  - (* The range is contained in b because every displayed value lies in b.     *)
    intros y H3. apply Range.Charac in H3. destruct H3 as [x H3].
    apply Charac2 in H3. destruct H3 as [H3 H4]. rewrite H4.
    apply H1. assumption.
Qed.

(* If the expression has exactly the values in b, it is onto b.                 *)
Proposition IsOnto : forall (f:U -> U) (a b:U),
  (forall x, x :< a -> f x :< b)                    ->
  (forall y, y :< b -> exists x, x :< a /\ f x = y) ->
  Onto (from a f) a b.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros f a b H1 H2. split. 1: apply IsFunctionOn.
  apply Incl.Double. split.
  - (* All displayed values lie in b.                                           *)
    intros y H3. apply Range.Charac in H3. destruct H3 as [x H3].
    apply Charac2 in H3. destruct H3 as [H3 H4]. rewrite H4.
    apply H1. assumption.
  - (* Every element of b is displayed by some element of a.                    *)
    intros y H3. apply H2 in H3. destruct H3 as [x [H3 H4]].
    apply Range.Charac. exists x. rewrite <- H4. apply Satisfies. assumption.
Qed.

(* If the expression is injective and has values b, it is a bijection a -> b.   *)
Proposition IsBij : forall (f:U -> U) (a b:U),
  (forall x, x :< a -> f x :< b)                          ->
  (forall x y, x :< a -> y :< a -> f x = f y -> x = y)    ->
  (forall y, y :< b -> exists x, x :< a /\ f x = y)       ->
  Bij (from a f) a b.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros f a b H1 H2 H3. split.
  - apply IsBijectionOn. assumption.
  - apply IsOnto; assumption.
Qed.
