Require Import ZF.Class.Equiv.
Require Import ZF.Class.Small.

(* Predicate on classes, determining whether a class is proper.                 *)
Definition Proper (P:Class) : Prop := ~Small P.
