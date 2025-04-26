Require Import ZF.Class.Core.
Require Import ZF.Class.Incl.
Require Import ZF.Class.Ordinal.Omega.
Require Import ZF.Set.Core.
Require Import ZF.Set.FromClass.
Require Import ZF.Set.Ordinal.Core.
Require Import ZF.Set.Ordinal.Natural.
Require Import ZF.Set.Ordinal.NonLimit.
Require Import ZF.Set.Ordinal.Succ.
Export ZF.Notation.N.

(* The set defined by the small class N. The set of natural numbers 0,1,2,...   *)
Definition omega : U := fromClass :N IsSmall.

(* Notation ":N" := omega                                                       *)
Global Instance SetN : N U := { omega := omega }.

(* Converting the set N to a class yields the class N.                          *)
Proposition ToClass : toClass :N :~: :N.
Proof.
  apply ToFromClass.
Qed.

(* A natural number is an ordinal whose successor contains non-limit ordinals.  *)
Proposition Charac : forall (n:U),
  n :< :N <-> Ordinal n /\ toClass (succ n) :<=: NonLimit.
Proof.
  intros n. split; intros H1.
  - apply FromClass.Charac in H1. assumption.
  - apply FromClass.Charac. assumption.
Qed.

(* Every element of N is an ordinal.                                            *)
Proposition IsOrdinal : forall (n:U), n :< :N -> Ordinal n.
Proof.
  intros n H1. apply Charac in H1. destruct H1 as [H1 _]. assumption.
Qed.

(* Every element of N is a non-limit ordinal.                                   *)
Proposition IsNonLimit : forall (n:U), n :< :N -> NonLimit n.
Proof.
  intros n H1. apply Charac in H1. destruct H1 as [_ H1]. apply H1, Succ.IsIn.
Qed.

(* 0 is a natural number.                                                       *)
Proposition HasZero : :0: :< :N.
Proof.
  apply FromClass.Charac, Class.Ordinal.Omega.HasZero.
Qed.

(* The successor of a natural number is a natural number.                       *)
Proposition HasSucc : forall (n:U), n :< :N -> succ n :< :N.
Proof.
  intros n H1. apply FromClass.Charac in H1. apply FromClass.Charac.
  apply Class.Ordinal.Omega.HasSucc. assumption.
Qed.

(* The set N is not empty.                                                      *)
Proposition NotEmpty : :N <> :0:.
Proof.
  intros H1. apply Empty.Charac with :0:.
  assert (:0: :< :N) as H2. { apply HasZero. }
  rewrite H1 in H2. assumption.
Qed.

(* An ordinal with non-limit ordinals as elements is a subset of N.             *)
Proposition IsSubset : forall (a:U),
  Ordinal a               ->
  toClass a :<=: NonLimit ->
  a :<=: :N.
Proof.
  intros a H1 H2. apply Incl.EquivCompatR with :N.
  - apply EquivSym, ToClass.
  - apply Class.Ordinal.Omega.IsSubclass; assumption.
Qed.

