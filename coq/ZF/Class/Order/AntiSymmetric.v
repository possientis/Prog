Require Import ZF.Class.
Require Import ZF.Set.
Require Import ZF.Set.OrdPair.

(* Predicate expressing the fact that R is an anti-symmetric class on A.        *)
Definition AntiSymmetric (R A:Class) : Prop := forall (x y:U), A x -> A y ->
  R :(x,y): -> R :(y,x): -> x = y.
