Declare Scope ZF_Class_Fun_scope.
Open    Scope ZF_Class_Fun_scope.

Require Import ZF.Class.
Require Import ZF.Class.Bijection.
Require Import ZF.Class.Domain.
Require Import ZF.Class.Incl.
Require Import ZF.Class.Function.
Require Import ZF.Class.Range.
Require Import ZF.Core.Equiv.
Require Import ZF.Core.Leq.

(* F is a function from A to B.                                                 *)
Definition Fun (F A B:Class) : Prop := FunctionOn F A /\ range F :<=: B.

(* F is a surjective function from A to B.                                      *)
Definition Onto (F A B:Class) : Prop := FunctionOn F A /\ range F :~: B.

(* F is an injective function from A to B.                                      *)
Definition Inj (F A B: Class) : Prop := BijectionOn F A /\ range F :<=: B.

(* F is a bijection from A to B.                                                *)
Definition Bij (F A B:Class) : Prop := BijectionOn F A /\ range F :~: B.

Notation "F :: A :-> B" := (Fun F A B)
  (at level 0, no associativity) : ZF_Class_Fun_scope.
