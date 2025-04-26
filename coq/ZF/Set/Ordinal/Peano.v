Require Import ZF.Class.Core.
Require Import ZF.Class.Incl.
Require Import ZF.Set.Core.
Require Import ZF.Set.Ordinal.Omega.
Require Import ZF.Set.Ordinal.Natural.
Require Import ZF.Set.Ordinal.Succ.

(* The set N (aka omega) satisfies the Peano axioms.                            *)

(* 0 belongs to N.                                                              *)
Proposition Peano1 : :0: :< :N.
Proof.
  apply HasZero.
Qed.

(* Every element has a successor.                                               *)
Proposition Peano2 : forall (n:U), n :< :N -> succ n :< :N.
Proof.
  apply HasSucc.
Qed.

(* 0 is a not a successor.                                                      *)
Proposition Peano3 : forall (n:U), n :< :N -> succ n <> :0:.
Proof.
  intros n _. apply Succ.NotEmpty.
Qed.

(* The successor function is injective.                                         *)
Proposition Peano4 : forall (n m:U), n :< :N -> m :< :N ->
  succ n = succ m -> n = m.
Proof.
  intros n m _ _. apply Succ.Injective.
Qed.

Proposition Peano5 : forall (A:Class),
  A :0:                                    ->
  (forall n, n :< :N -> A n -> A (succ n)) ->
  toClass :N :<=: A.
Proof.
  apply Induction.
Qed.

