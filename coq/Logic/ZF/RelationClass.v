Require Import Logic.ZF.Class.
Require Import Logic.ZF.Core.
Require Import Logic.ZF.OrdPair.

(* Predicate on classes, expressing the fact that a class is a 'relation class' *)
(* i.e. a class whose 'elements' are ordered pairs.                             *)
Definition RelClass (R:Class) : Prop :=
    forall x, R x -> exists y, exists z, x = :(y,z):.

