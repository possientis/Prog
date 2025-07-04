Require Import ZF.Class.Equiv.
Require Import ZF.Class.Diff.
Require Import ZF.Class.Incl.
Require Import ZF.Class.Less.
Require Import ZF.Class.Ordinal.Core.
Require Import ZF.Class.Ordinal.Inf.
Require Import ZF.Class.Small.
Require Import ZF.Set.Core.

Require Import ZF.Notation.InfAbove.
Export ZF.Notation.InfAbove.

(* The infimum of the class A above b.                                          *)
Definition infAbove (b:U)(A:Class) : Class := inf (A :\: toClass b).

(* Notation "inf(>: b ) A" := (infAbove b A)                                    *)
Global Instance ClassInfAbove : InfAbove Class := { infAbove := infAbove }.

(* The infimum of a class above b is an ordinal class.                          *)
Proposition IsOrdinal : forall (A:Class) (b:U),
  Ordinal (inf(>: b) A).
Proof.
  intros A b. apply Ordinal.Inter.IsOrdinal, Class.Inter2.IsInclR.
Qed.

(* The infimum of a class above b is small.                                     *)
Proposition IsSmall : forall (A:Class) (b:U),
  Small (inf(>: b) A).
Proof.
  intros A b. apply Inter.IsSmall.
Qed.

(* The infimum of a class above b is a strict subclass of On.                   *)
Proposition IsLess : forall (A:Class) (b:U),
  inf(>: b) A :<: On.
Proof.
  intros A b.
  assert (inf(>: b) A :~: On \/ inf(>: b) A :<: On) as H1. {
    apply Core.IsOnOrLess, IsOrdinal. }
  destruct H1 as [H1|H1]. 2: assumption. exfalso.
  apply OnIsProper. apply Small.EquivCompat with (inf(>: b) A).
  1: assumption. apply IsSmall.
Qed.
