Require Import ZF.Class.Incl.
Require Import ZF.Class.Equiv.
Require Import ZF.Class.Order.E.
Require Import ZF.Class.Ordinal.Core.
Require Import ZF.Class.Ordinal.Order.
Require Import ZF.Class.Relation.Function.

Module COO := ZF.Class.Ordinal.Order.

(* The class A is intended to be a class of ordinals.                           *)
Definition SmallestFresh (A:Class) : Class := COO.SmallestFresh E A.

Proposition IsFunction : forall (A:Class),
  A :<=: On -> Function (SmallestFresh A).
Proof.
Admitted.

