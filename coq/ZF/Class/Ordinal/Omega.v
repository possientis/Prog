Require Import ZF.Class.Core.
Require Import ZF.Class.Incl.
Require Import ZF.Class.Ordinal.Core.
Require Import ZF.Class.Ordinal.NonLimit.
Require Import ZF.Set.Ordinal.Succ.

(* The class natural numbers.                                                   *)
Definition omega : Class := fun a =>
  On a /\ toClass (succ a) :<=: NonLimit.
