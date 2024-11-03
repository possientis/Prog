Declare Scope ZF_Infinite_scope.
Open    Scope ZF_Infinite_scope.

Require Import Logic.ZF.Core.
Require Import Logic.ZF.Empty.
Require Import Logic.ZF.Singleton.
Require Import Logic.ZF.Union.

(* There exists a set containing the empty set and such that if x is an element *)
(* then so is x :\/: :{x}:                                                      *)
Axiom Infinite : exists a, :0: :< a /\ forall x, x :< a -> x :\/: :{x}: :< a.
