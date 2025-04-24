Require Import ZF.Set.Core.
Require Import ZF.Set.Empty.
Require Import ZF.Set.Single.
Require Import ZF.Set.Union2.

(* There exists a set containing the empty set and such that if x is an element *)
(* then so is x :\/: :{x}:                                                      *)
Axiom Infinity : exists a, :0: :< a /\ forall x, x :< a -> x :\/: :{x}: :< a.
