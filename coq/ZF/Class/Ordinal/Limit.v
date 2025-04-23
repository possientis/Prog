Require Import ZF.Class.Core.
Require Import ZF.Class.Diff.
Require Import ZF.Class.Incl.
Require Import ZF.Class.Inter.
Require Import ZF.Class.Ordinal.Core.
Require Import ZF.Class.Ordinal.NonLimit.

(* The class of limit ordinals.                                                 *)
Definition Limit : Class := On :\: NonLimit.

(* Limit is a class of ordinals.                                                *)
Proposition LimitIsOrdinal : Limit :<=: On.
Proof.
  apply Inter.InclL.
Qed.

