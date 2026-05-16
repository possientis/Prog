Require Import ZF.Class.Equiv.
Require Import ZF.Set.Core.
Require Import ZF.Set.Cardinal.Equiv.
Require Import ZF.Set.Ordinal.Omega.


(* The class of finite sets, those equipotent to some natural number.           *)
Definition Finite : Class := fun a =>
  exists n, n :< :N /\ a :~: n.
