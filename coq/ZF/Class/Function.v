Require Import ZF.Class.
Require Import ZF.Class.Functional.
Require Import ZF.Class.Rel.

(* A class is a function iff it is a relation and it is functional.             *)
Definition Function (F:Class) : Prop := Rel F /\ Functional F.
