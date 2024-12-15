Require Import ZF.Core.Zero.
Require Import ZF.Set.
Require Import ZF.Set.Empty.
Require Import ZF.Set.Singleton.
Require Import ZF.Set.Union.

(* There exists a set containing the empty set and such that if x is an element *)
(* then so is x :\/: :{x}:                                                      *)
Axiom Infinite : exists a, :0: :< a /\ forall x, x :< a -> x :\/: :{x}: :< a.
