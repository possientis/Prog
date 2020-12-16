Require Import Logic.Axiom.Sat.

(* A proposition has a semi-decider                                             *)
Definition Sec (A:Prop) : Type := sig (fun f => A <-> tsat f). 


