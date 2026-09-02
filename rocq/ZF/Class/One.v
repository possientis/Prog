Require Import ZF.Class.Equiv.
Require Import ZF.Set.Core.
Require Import ZF.Set.Empty.

Require Import ZF.Notation.One.
Export ZF.Notation.One.

Definition one : Class := fun x => x = :0:.

Global Instance ClassOne : One Class := { one := one }.
