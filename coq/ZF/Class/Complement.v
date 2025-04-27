Require Import ZF.Class.Core.
Require Import ZF.Set.Core.

Require Import ZF.Notation.Not.
Export ZF.Notation.Not.

(* Complement of a class.                                                       *)
Definition complement (P:Class) : Class := fun x => ~ (P x).

(* Notation ":¬: P" := (complement P)                                           *)
Global Instance ClassNot : Not Class := { not := complement }.
