Require Import Logic.Axiom.Sat.
Require Import Logic.Axiom.Dec.

(* Computational omni-science.                                                  *)
Definition CO : Prop := Decidable (tsat). 
