Require Import ZF.Class.
Require Import ZF.Set.OrdPair.

(* A relation class is a class whose elements are ordered pairs.                *)
Definition Relation (P:Class) : Prop :=
    forall x, P x -> exists y, exists z, x = :(y,z):.
