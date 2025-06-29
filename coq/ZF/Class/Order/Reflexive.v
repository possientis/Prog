Require Import ZF.Class.Equiv.
Require Import ZF.Set.Core.
Require Import ZF.Set.OrdPair.

(* Predicate expressing the fact that R is a reflexive class on A.              *)
Definition Reflexive (R A:Class) : Prop := forall (x:U), A x -> R :(x,x):.
