Require Import ZF.Class.Equiv.
Require Import ZF.Set.Core.
Require Import ZF.Set.OrdPair.

(* Predicate expressing the fact that R is a transitive class on A.             *)
Definition Transitive (R A:Class) : Prop := forall (x y z:U), A x -> A y -> A z ->
  R :(x,y): -> R :(y,z): -> R :(x,z):.
