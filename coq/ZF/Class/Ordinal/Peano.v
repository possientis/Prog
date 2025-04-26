Require Import ZF.Class.Core.
Require Import ZF.Class.Incl.
Require Import ZF.Class.Ordinal.Omega.
Require Import ZF.Set.Core.
Require Import ZF.Set.Ordinal.Natural.
Require Import ZF.Set.Ordinal.Succ.

(* The class N (aka omega) satisfies the Peano axioms.                          *)

(* 0 belongs to the class. The type annotation is needed for class resolution.  *)
Proposition Peano1 : (:N : Class) :0:.
Proof.
  apply HasZero.
Qed.

(* Every element has a successor. The type annotation is needed here too.       *)
Proposition Peano2 : forall (i:U), (:N : Class) i -> (:N : Class) (succ i).
Proof.
  apply HasSucc.
Qed.

(* 0 is a not a successor. The type annotation is needed,                       *)
Proposition Peano3 : forall (i:U), (:N : Class) i -> succ i <> :0:.
Proof.
  intros i _. apply Succ.NotEmpty.
Qed.

(* The successor function is injective. The type annotation is needed.          *)
Proposition Peano4 : forall (i j:U), (:N : Class) i -> (:N : Class) j ->
  succ i = succ j -> i = j.
Proof.
  intros i j _ _. apply Succ.Injective.
Qed.

Proposition Peano5 : forall (A:Class),
  A :0:                                           ->
  (forall i, (:N : Class) i -> A i -> A (succ i)) ->
  :N :<=: A.
Proof.
  apply Induction.
Qed.
