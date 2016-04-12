Set Implicit Arguments.
Require Import Arith.

Print sum.
(* Inductive sum (A B : Type) : Type :=  inl : A -> A + B | inr : B -> A + B *)

Check (sum nat bool). (* Set *)

Check (inl bool 4). (* nat + bool *) 
