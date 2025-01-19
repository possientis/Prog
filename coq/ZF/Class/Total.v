Require Import ZF.Class.
Require Import ZF.Set.
Require Import ZF.Set.OrdPair.

(* Predicate expressing the fact that R is a total class on A.                  *)
Definition Total (R A:Class) : Prop := forall (x y:U), A x -> A y ->
  x = y \/ R :(x,y): \/ R :(y,x):.

