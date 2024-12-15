Require Import ZF.Class.
Require Import ZF.Core.Diff.

Definition difference (P Q:Class) : Class := fun x => P x /\ ~ Q x.

(* Notation "P :\: Q" := (difference P Q)                                       *)
Global Instance ClassDiff : Diff Class := { diff := difference }.
