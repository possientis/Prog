Require Import ZF.Class.Equiv.
Require Import ZF.Class.Order.WellOrdering.
Require Import ZF.Set.Core.
Require Import ZF.Set.Order.Founded.
Require Import ZF.Set.Order.Total.
Require Import ZF.Set.Order.Transport.
Require Import ZF.Set.Relation.Bij.

Module COW := ZF.Class.Order.WellOrdering.

(* Predicate expressing the fact that r is a well-ordering set on a.            *)
(* r is a well-ordering on a iff it is founded on a and total on a.             *)
Definition WellOrdering (r a:U) : Prop :=  Founded r a /\ Total r a.

Proposition ToClass : forall (r a:U),
  WellOrdering r a -> COW.WellOrdering (toClass r) (toClass a).
Proof.
  intros r a H1. assumption.
Qed.

Proposition FromClass : forall (r a:U),
  COW.WellOrdering (toClass r) (toClass a) -> WellOrdering r a.
Proof.
  intros r a H1. assumption.
Qed.

(* Well-ordering is preserved under transport by a bijection.                   *)
Proposition Transport : forall (f r s a b:U),
  s = transport f r a  ->
  Bij f a b            ->
  WellOrdering r a     ->
  WellOrdering s b.
Proof.
  (* Proof by Claude.                                                           *)
  intros f r s a b H1 H2 [H3 H4]. split.
  - apply (Founded.Transport f r s a b); assumption.
  - apply (Total.Transport f r s a b); assumption.
Qed.
