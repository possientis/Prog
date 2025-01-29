Require Import ZF.Binary.
Require Import ZF.Binary.Converse.
Require Import ZF.Binary.Functional.

(* A binary class is one-to-one if it is functional and so is its converse.     *)
Definition OneToOne (F:Binary) : Prop := Functional F /\ Functional F^:-1:.
