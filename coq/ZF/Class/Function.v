Require Import ZF.Class.
Require Import ZF.Class.Functional.
Require Import ZF.Class.Relation.

(* A class is a function if it is a relation and it is functional.              *)
Definition Function (P:Class) : Prop := Relation P /\ Functional P.
