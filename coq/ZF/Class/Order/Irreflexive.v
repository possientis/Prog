Require Import ZF.Class.Core.
Require Import ZF.Set.Core.
Require Import ZF.Set.OrdPair.

(* Predicate expressing the fact that R is an irreflexive class on A.           *)
Definition Irreflexive (R A:Class) : Prop := forall (x:U), A x -> ~ R :(x,x):.
