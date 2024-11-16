Require Import ZF.Axiom.Core.
Require Import ZF.Axiom.Union.
Require Import ZF.Set.Empty.
Require Import ZF.Set.Singleton.

(* There exists a set containing the empty set and such that if x is an element *)
(* then so is x :\/: :{x}:                                                      *)
Axiom Infinite : exists a, :0: :< a /\ forall x, x :< a -> x :\/: :{x}: :< a.
