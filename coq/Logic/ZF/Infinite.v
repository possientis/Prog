Declare Scope ZF_Infinite_scope.
Open    Scope ZF_Infinite_scope.

Require Import Logic.ZF.Core.
Require Import Logic.ZF.Singleton.
Require Import Logic.ZF.Union.

(* This axiom asserts the existence of at least one set, so the universe of set *)
(* is not empty.                                                                *)

Axiom Infinite : exists a,
  (forall y, (forall x, ~ x :< y) -> y :< a) /\
  (forall x, x :< a -> x :\/: :{x}: :< a).
