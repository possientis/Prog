Require Import ZF.Class.Incl.
Require Import ZF.Class.Equiv.
Require Import ZF.Class.Order.E.
Require Import ZF.Class.Ordinal.Core.
Require Import ZF.Class.Ordinal.Isom.
Require Import ZF.Class.Relation.Function.

Module COI := ZF.Class.Ordinal.Isom.

(* The class A is intended to be a class of ordinals.                           *)
Definition SmallestFresh (A:Class) : Class := COI.SmallestFresh E A.

Proposition IsFunction : forall (A:Class),
  A :<=: On -> Function (SmallestFresh A).
Proof.
Admitted.

