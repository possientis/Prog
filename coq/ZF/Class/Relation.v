Require Import ZF.Class.
Require Import ZF.Set.OrdPair.

(* A class is a relation, iff its 'elements' are ordered pairs.                 *)
Definition Relation (P:Class) : Prop :=
    forall x, P x -> exists y, exists z, x = :(y,z):.
