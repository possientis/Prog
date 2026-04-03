Require Import ZF.Class.Incl.
Require Import ZF.Class.Equiv.
Require Import ZF.Class.Ordinal.Transitive.
Require Import ZF.Set.Core.
Require Import ZF.Set.Power.


(* Predicate defining a supertransitive class.                                  *)
Definition Super (A:Class) : Prop := Transitive A /\
  forall x, A x -> toClass :P(x) :<=: A.


