Set Implicit Arguments.
Require Import List.
Require Import Arith.

Require Import set.
Require Import subset.

(******************************************************************************)
(*                        equiv : set -> set -> Prop                          *)
(******************************************************************************)

Definition equiv (a b:set) : Prop := (subset a b) /\ (subset b a).

