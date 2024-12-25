Require Import ZF.Binary.
Require Import ZF.Binary.Functional.

(* A binary class is a function if and only if it is functional                 *)
Definition Function (F:Binary) : Prop := Functional F.
