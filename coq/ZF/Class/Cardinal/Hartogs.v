Require Import ZF.Class.Equiv.
Require Import ZF.Set.Core.
Require Import ZF.Set.Ordinal.Core.
Require Import ZF.Set.Relation.Inj.

Definition hartogs (a:U) : Class := fun b =>
  Ordinal b /\ exists f, Inj f b a.
