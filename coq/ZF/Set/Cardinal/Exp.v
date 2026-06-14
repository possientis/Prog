Require Import ZF.Set.Core.
Require Import ZF.Set.Relation.Map.

Require Import ZF.Notation.Exp2.
Export ZF.Notation.Exp2.

(* The exponentiation of two sets.                                              *)
Definition exp (a b:U) : U := map b a.


(* Notation "a :^^: b" := (exp a b)                                              *)
Global Instance SetExp2 : Exp2 U := { exp2 := exp }.

