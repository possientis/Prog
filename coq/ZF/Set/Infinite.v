Require Import ZF.Class.Equiv.
Require Import ZF.Set.Core.
Require Import ZF.Set.Finite.


(* The class of infinite sets, those which are not finite.                      *)
Definition Infinite : Class := fun a => ~ Finite a.
