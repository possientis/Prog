Require Import ZF.Class.Core.
Require Import ZF.Class.Diff.
Require Import ZF.Class.Incl.
Require Import ZF.Class.Inter.
Require Import ZF.Class.Inter2.
Require Import ZF.Class.Less.
Require Import ZF.Class.Ordinal.Core.
Require Import ZF.Class.Ordinal.Inter.
Require Import ZF.Class.Small.
Require Import ZF.Set.Core.
Require Import ZF.Set.FromClass.

Require Import ZF.Notation.InfAbove.
Export ZF.Notation.InfAbove.

(* The infimum of the class A. (using tweaked intersection, so 0 when 0).       *)
Definition inf (A:Class) : Class := :J(A :/\: On).

(* The infimum of the class A above b.                                          *)
Definition infAbove (b:U)(A:Class) : Class := inf (A :\: toClass b).

(* Notation "inf(>: b ) A" := (infAbove b A)                                    *)
Global Instance ClassInfAbove : InfAbove Class := { infAbove := infAbove }.

(* The infimum operation is compatible with class equivalence.                  *)
Proposition EquivCompat : forall (A B:Class),
  A :~: B -> inf A :~: inf B.
Proof.
  intros A B H1. apply Inter.EquivCompat', Inter2.EquivCompatL. assumption.
Qed.

(* The infimum of a class of ordinals coincide with its (tweaked) intersection. *)
Proposition WhenHasOrdinalElem : forall (A:Class),
  A :<=: On -> inf A :~: :J(A).
Proof.
  intros A H1. unfold inf. apply Inter.EquivCompat'.
  intros x. split; intros H2.
  - apply H2.
  - split. 1: assumption. apply H1. assumption.
Qed.

(* The infimum of a class is an ordinal class.                                 *)
Proposition IsOrdinal : forall (A:Class), Ordinal (inf A).
Proof.
  intros A. apply Ordinal.Inter.IsOrdinal', Class.Inter2.InclR.
Qed.

(* The infimum of a class above b is an ordinal class.                          *)
Proposition IsOrdinalAbove : forall (A:Class) (b:U),
  Ordinal (inf(>: b) A).
Proof.
  intros A b. apply Ordinal.Inter.IsOrdinal', Class.Inter2.InclR.
Qed.

(* The infimum of a class is small.                                             *)
Proposition IsSmall : forall (A:Class), Small (inf A).
Proof.
  intros A. apply Inter.IsSmall'.
Qed.

(* The infimum of a class above b is small.                                     *)
Proposition IsSmallAbove : forall (A:Class) (b:U),
  Small (inf(>: b) A).
Proof.
  intros A b. apply Inter.IsSmall'.
Qed.

(* The infimum of a class is a strict subclass of On.                           *)
Proposition IsLess : forall (A:Class), inf A :<: On.
Proof.
  intros A.
  assert (inf A :~: On \/ inf A :<: On) as H1. {
    apply Core.IsEquivOrLess, IsOrdinal. }
  destruct H1 as [H1|H1]. 2: assumption. exfalso.
  apply OnIsProper. apply Small.EquivCompat with (inf A).
  1: assumption. apply IsSmall.
Qed.

(* The infimum of a class above b is a strict subclass of On.                   *)
Proposition IsLessAbove : forall (A:Class) (b:U),
  inf(>: b) A :<: On.
Proof.
  intros A b.
  assert (inf(>: b) A :~: On \/ inf(>: b) A :<: On) as H1. {
    apply Core.IsEquivOrLess, IsOrdinalAbove. }
  destruct H1 as [H1|H1]. 2: assumption. exfalso.
  apply OnIsProper. apply Small.EquivCompat with (inf(>: b) A).
  1: assumption. apply IsSmallAbove.
Qed.

(* The set of the class 'inf A' is an ordinal.                                  *)
Proposition IsOrdinalAsSet : forall (A:Class) (a:U),
  IsSetOf (inf A) a -> On a.
Proof.
  intros A a H1. apply Core.EquivCompat with (inf A).
  - apply EquivSym. assumption.
  - apply IsOrdinal.
Qed.

(* The set of the class 'inf(>: b) A' is an ordinal.                            *)
Proposition IsOrdinalAsSetAbove : forall (A:Class) (a b:U),
  IsSetOf (inf(>: b) A) a -> On a.
Proof.
  intros A a b H1. apply Core.EquivCompat with (inf(>: b) A).
  - apply EquivSym. assumption.
  - apply IsOrdinalAbove.
Qed.
