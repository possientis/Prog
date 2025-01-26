Require Import ZF.Binary.
Require Import ZF.Core.Equiv.
Require Import ZF.Core.Inverse.

(* The converse of a binary class.                                              *)
Definition converse (F:Binary) : Binary := fun x y => F y x.

(* Notation "F ^:-1:" := (converse F)                                           *)
Global Instance BinaryInverse : Inverse Binary := { inverse := converse }.

(* Taking the converse is an indempotent operation.                             *)
(* Note that we have actual equality here, not just equivalence.                *)
Proposition ConverseIdempotent : forall (F:Binary),
  (F^:-1:)^:-1: = F.
Proof.
  intros F. unfold converse. reflexivity.
Qed.

(* The converse operation is compatible with equivalence.                       *)
Proposition ConverseEquivCompat : forall (F G:Binary),
  F :~: G -> F^:-1: :~: G^:-1:.
Proof.
  intros F G H1 x y. unfold converse. apply H1.
Qed.
