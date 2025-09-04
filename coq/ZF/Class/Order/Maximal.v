Require Import ZF.Class.Equiv.
Require Import ZF.Set.Core.
Require Import ZF.Set.OrdPair.

(* Predicate expressing the fact that a is an R-maximal element of A.           *)
Definition Maximal (R A:Class) (a:U) : Prop
  := A a /\ (forall x, A x -> ~ R :(a,x):).
