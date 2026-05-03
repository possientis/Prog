Require Import ZF.Class.Equiv.
Require Import ZF.Class.Order.StrictTotalOrd.
Require Import ZF.Set.Core.
Require Import ZF.Set.Order.StrictOrd.
Require Import ZF.Set.Order.Total.
Require Import ZF.Set.OrdPair.

Module COS := ZF.Class.Order.StrictTotalOrd.

(* Predicate expressing the fact that r is a strict total order set on a.       *)
Definition StrictTotalOrd (r a:U) : Prop := StrictOrd r a /\ Total r a.
