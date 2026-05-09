Require Import ZF.Class.Equiv.
Require Import ZF.Class.Order.StrictOrd.
Require Import ZF.Set.Core.
Require Import ZF.Set.Order.Irreflexive.
Require Import ZF.Set.Order.Transitive.
Require Import ZF.Set.Order.Transport.
Require Import ZF.Set.OrdPair.
Require Import ZF.Set.Relation.Bij.

Module COS := ZF.Class.Order.StrictOrd.

(* Predicate expressing the fact that r is a strict order on a                  *)
Definition StrictOrd (r a:U) : Prop := Irreflexive r a /\ Transitive r a.

(* If the sets forma strict order, then so do the classes.                      *)
Proposition ToClass : forall (r a:U),
  StrictOrd r a -> COS.StrictOrd (toClass r) (toClass a).
Proof.
  intros r a H1. assumption.
Qed.

(* If the classes form a strict order, then so do the sets.                     *)
Proposition FromClass : forall (r a:U),
  COS.StrictOrd (toClass r) (toClass a) -> StrictOrd r a.
Proof.
  intros r a H1. assumption.
Qed.

(* In a strict order, if x < y then neither x = y nor y < x holds.              *)
Proposition WhenLess : forall (r a x y:U),
  StrictOrd r a               ->
  x :< a                      ->
  y :< a                      ->
  :(x,y): :< r                ->
  ~ (x = y \/ :(y,x): :< r).
Proof.
  (* Proof by Claude.                                                           *)
  intros r a x y [H3 H4] H1 H2 H5 H6. destruct H6 as [H6|H6].
  - subst. apply H3 with y. 1: assumption. assumption.
  - apply H3 with x. 1: assumption. apply H4 with y; assumption.
Qed.

(* Strict order is preserved under transport by a bijection.                    *)
Proposition Transport : forall (f r s a b:U),
  s = transport f r a ->
  Bij f a b           ->
  StrictOrd r a       ->
  StrictOrd s b.
Proof.
  (* Proof by Claude.                                                           *)
  intros f r s a b H1 H2 [H3 H4]. split.
  - apply (Irreflexive.Transport f r s a b); assumption.
  - apply (Transitive.Transport f r s a b); assumption.
Qed.
