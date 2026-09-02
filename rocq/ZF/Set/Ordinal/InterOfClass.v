Require Import ZF.Axiom.Classic.
Require Import ZF.Class.Equiv.
Require Import ZF.Class.Empty.
Require Import ZF.Class.Ordinal.OrdClass.
Require Import ZF.Class.Ordinal.Inter.
Require Import ZF.Class.Incl.
Require Import ZF.Class.Inter.
Require Import ZF.Set.Core.
Require Import ZF.Set.Empty.
Require Import ZF.Set.InterOfClass.
Require Import ZF.Set.Ordinal.Ordinal.

Module CIN := ZF.Class.Incl.
Module COI := ZF.Class.Ordinal.Inter.


(* This is a more general treatment of ZF.Set.Ordinal.Inter where we use inter  *)
(* as defined in ZF.Set.InterOfClass which allows for class argument.           *)

(* The intersection of a class of ordinals is an ordinal.                       *)
Proposition IsOrdinal : forall (A:Class),
  A :<=: Ordinal -> Ordinal (inter A).
Proof.
  intros A H1. apply OrdClass.EquivCompat with :I(A).
  - apply Equiv.Sym, InterOfClass.ToClass.
  - apply COI.IsOrdinal. assumption.
Qed.

(* The intersection of a class of ordinals is a lower-bound of the class.       *)
Proposition IsLowerBound : forall (A:Class) (a:U),
  A :<=: Ordinal  ->
  A a             ->
  inter A :<=: a.
Proof.
  intros A a H1 H2. apply CIN.EquivCompatL with :I(A).
  - apply Equiv.Sym, InterOfClass.ToClass.
  - apply COI.IsLowerBound; assumption.
Qed.

(* The intersection of a class of ordinals is the largest lower-bound.          *)
Proposition IsLargest : forall (A:Class) (a:U),
  A :<=: Ordinal              ->
  A :<>: :0:                  ->
  (forall b, A b -> a :<=: b) ->
  a :<=: inter A.
Proof.
  intros A a H1 H2 H3. apply CIN.EquivCompatR with :I(A).
  - apply Equiv.Sym, InterOfClass.ToClass.
  - apply COI.IsLargest; assumption.
Qed.

(* The intersection of an ordinal class is 0.                                   *)
Proposition IsZero : forall (A:Class),
  OrdClass.Ordinal A -> inter A = :0:.
Proof.
  intros A H1.
  assert (A :~: :0: \/ A :<>: :0:) as H2. { apply LawExcludedMiddle. }
  destruct H2 as [H2|H2].
  - rewrite <- InterOfClass.IsZero. apply InterOfClass.EquivCompat. assumption.
  - apply Incl.Double. split; intros x H3.
    + apply InterOfClass.Charac with A. 1: assumption.
      apply OrdClass.HasZero; assumption.
    + apply Empty.Charac in H3. contradiction.
Qed.
