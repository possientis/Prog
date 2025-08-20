Require Import ZF.Class.Equiv.
Require Import ZF.Set.Core.
Require Import ZF.Set.Empty.
Require Import ZF.Set.Incl.
Require Import ZF.Set.Ordinal.Core.
Require Import ZF.Set.Ordinal.Limit.
Require Import ZF.Set.Ordinal.Omega.
Require Import ZF.Set.Ordinal.Recursion2OfClass.
Require Import ZF.Set.Ordinal.Succ.
Require Import ZF.Set.Relation.Eval.
Require Import ZF.Set.Relation.FunctionOn.

Module SOR2 := ZF.Set.Ordinal.Recursion2OfClass.

(*
Require Import ZF.Class.Ordinal.Induction2.
Require Import ZF.Class.Ordinal.Recursion2.
Require Import ZF.Set.Empty.
Require Import ZF.Set.Incl.
Require Import ZF.Set.Ordinal.Core.
Require Import ZF.Set.Ordinal.Limit.
Require Import ZF.Set.Ordinal.Succ.
Require Import ZF.Set.Relation.Eval.
Require Import ZF.Set.Relation.FunctionOn.
Require Import ZF.Set.Relation.RestrictOfClass.
Require Import ZF.Set.Union.
Require Import ZF.Set.UnionGen.
Require Import ZF.Set.UnionGenOfClass.
*)


(* The recursion set associated with the class F and set a.                     *)
(* In other words, the unique function f defined on N by the equations:         *)
(* (i)    f(0)      = a                                                         *)
(* (ii)   f(n+1) = F(f(n))                                                      *)
Definition recursion (F:Class) (a:U) : U := (SOR2.recursion F a :N).

(* The recursion set of F and a is a function defined on N.   *)
Proposition IsFunctionOn : forall (F:Class) (a:U),
  FunctionOn (recursion F a) :N.
Proof.
  intros F a. apply (SOR2.IsFunctionOn F a :N), Omega.IsOrdinal.
Qed.

(* The recursion set of F and a has initial value a.                            *)
Proposition WhenZero : forall (F:Class) (a:U),
  (recursion F a)!:0: = a.
Proof.
  intros F a. apply (SOR2.WhenZero F a :N).
  - apply Omega.IsOrdinal.
  - apply Omega.IsNotEmpty.
Qed.

(* The recursion set satisfies the equation f(n+1) = F(f(n)).                   *)
Proposition WhenSucc : forall (F:Class) (a n:U),
  n :< :N                                            ->
  (recursion F a)!(succ n)  = F!((recursion F a)!n).
Proof.
  intros F a n H1. apply (SOR2.WhenSucc F a :N).
  - apply Omega.IsOrdinal.
  - apply Omega.HasSucc. assumption.
Qed.

(* The recursion set of F a is the unique function f defined on N such that     *)
(* f(0) = a and f(n+1) = F(f(n)) for all n.                                     *)
Proposition IsUnique : forall (F:Class) (a f:U),
  FunctionOn f :N                               ->
  f!:0: = a                                     ->    (* (i)  *)
  (forall n, n :< :N -> f!(succ n) = F!(f!n))   ->    (* (ii) *)
  f = recursion F a.
Proof.
  intros F a f H1 H2 H3. apply (SOR2.IsUnique F a :N); try assumption.
  - apply Omega.IsOrdinal.
  - intros n H4 H5. apply H3. apply Core.ElemIsIncl in H5. 2: apply Omega.IsOrdinal.
    apply H5, Succ.IsIn.
  - intros n H4 H5. destruct H4 as [H4 H6]. exfalso. apply H6.
    apply Omega.HasNonLimitElem. assumption.
Qed.
