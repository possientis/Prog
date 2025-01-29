Require Import ZF.Binary.
Require Import ZF.Core.Dot.
Export ZF.Core.Dot.

(* Composition of two binary relation.                                          *)
Definition compose (G F:Binary) : Binary := fun x z =>
  exists y, F x y /\ G y z.

(* Notation "G :.: F" := (compose G F)                                          *)
Global Instance BinaryDot : Dot Binary := { dot := compose }.
