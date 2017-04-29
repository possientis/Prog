Require Import set.
Require Import subset.

(******************************************************************************)
(*                        belong : set -> set -> Prop                         *)
(******************************************************************************)

Definition belong (a b:set) : Prop := subset (Singleton a) b. 
