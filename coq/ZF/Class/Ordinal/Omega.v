Require Import ZF.Class.Core.
Require Import ZF.Class.Empty.
Require Import ZF.Class.Incl.
Require Import ZF.Class.Ordinal.Core.
Require Import ZF.Class.Ordinal.NonLimit.
Require Import ZF.Set.Core.
Require Import ZF.Set.Ordinal.Natural.
Require Import ZF.Set.Ordinal.Succ.
Require Import ZF.Set.Single.
Require Import ZF.Set.Union2.

Require Import ZF.Notation.N.
Export ZF.Notation.N.

(* The class natural numbers.                                                   *)
Definition omega : Class := fun a =>
  On a /\ toClass (succ a) :<=: NonLimit.

(* Notation ":N" := omega                                                       *)
Global Instance ClassN : N Class := { omega := omega }.

(* 0 belongs to the class omega. The notation ':N' can't be used here.          *)
Proposition HasZero : omega :0:.
Proof.
  split.
  - apply ZeroIsOrdinal.
  - intros a H1. apply Union2.Charac in H1. destruct H1 as [H1|H1].
    + apply Empty.Charac in H1. contradiction.
    + apply Single.Charac in H1. subst. left. reflexivity.
Qed.


(*
Proposition NotEmpty : :N :<>: :0:.
Proof.
  intros H1. apply Class.Empty.Charac with :0:. apply H1. split.
  - apply ZeroIsOrdinal.
  - intros a H2. apply Union2.Charac in H2.

Show.
*)
