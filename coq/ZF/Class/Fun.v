Declare Scope ZF_Class_Fun_scope.
Open    Scope ZF_Class_Fun_scope.

Require Import ZF.Class.
Require Import ZF.Class.Incl.
Require Import ZF.Class.FunctionOn.
Require Import ZF.Class.Range.

(* F is a function from A to B.                                                 *)
Definition Fun (F A B:Class) : Prop := FunctionOn F A /\ range F :<=: B.

Notation "F :: A :-> B" := (Fun F A B)
  (at level 0, no associativity) : ZF_Class_Fun_scope.
