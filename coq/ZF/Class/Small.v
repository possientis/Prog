Require Import ZF.Class.
Require Import ZF.Set.

(* Predicate on classes, stating that a class is actually a set.                *)
Definition Small (P:Class) : Prop := exists a, forall x, x :< a <-> P x.

(* Predicate on classes, determining whether a class is proper.                 *)
Definition Proper (P:Class) : Prop := ~Small P.
