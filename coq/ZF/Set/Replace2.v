Require Import ZF.Class.
Require Import ZF.Class.Functional.
Require Import ZF.Class.Image.
Require Import ZF.Class.Small.
Require Import ZF.Set.

(* The image of a small class by a functional class is small.                   *)
Proposition ReplaceSmall : forall (P Q:Class),
  Functional P -> Small Q -> Small P :[Q]:.
Proof.

Show.
