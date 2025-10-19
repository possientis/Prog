Require Import ZF.Class.Equiv.
Require Import ZF.Class.Order.WellOrdering.
Require Import ZF.Set.Core.
Require Import ZF.Set.Order.Founded.
Require Import ZF.Set.Order.Total.

Module COW := ZF.Class.Order.WellOrdering.

(* Predicate expressing the fact that r is a well-ordering set on a.            *)
(* r is a well-ordering on a iff it is founded on a and total on a.             *)
Definition WellOrdering (r a:U) : Prop :=  Founded r a /\ Total r a.

Proposition ToClass : forall (r a:U),
  WellOrdering r a <-> COW.WellOrdering (toClass r) (toClass a).
Proof.
  intros r a. split; intros [H1 H2]; split; assumption.
Qed.
