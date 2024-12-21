Require Import ZF.Binary.
Require Import ZF.Binary.Image.
Require Import ZF.Binary.Range.
Require Import ZF.Class.
Require Import ZF.Core.Pipe.
Require Import ZF.Set.

(* Restricting a binary class F to a class P.                                   *)
Definition restrict (F:Binary) (P:Class) : Binary := fun x y =>
  P x /\ F x y.

(* Notation "F :|: P" := (restrict F P)                                         *)
Global Instance BinaryPipe : Pipe Binary Class := { pipe := restrict }.

(* Image is the range of the restriction.                                       *)
(* This is an equal equality, not just equivalence.                             *)
Proposition ImageIsRestriction : forall (F:Binary) (P:Class),
  F:[P]: = range (F:|:P).
Proof.
  intros F P. unfold image, range, restrict. reflexivity.
Qed.
