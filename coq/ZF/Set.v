Require Import ZF.Core.Elem.
Export ZF.Core.Elem.

(* There is a universe of sets                                                  *)
Axiom U : Type.

(* There is a fundamental membership predicate between sets                     *)
Axiom Elem : U -> U -> Prop.

(* Notation "x :< y" := (Elem x y)                                              *)
Global Instance SetElem : Core.Elem.Elem U U := { elem := Elem }.

