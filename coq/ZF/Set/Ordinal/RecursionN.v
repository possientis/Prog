Require Import ZF.Class.Equiv.
Require Import ZF.Set.Core.
Require Import ZF.Set.Empty.
Require Import ZF.Set.Incl.
Require Import ZF.Set.Ordinal.Core.
Require Import ZF.Set.Ordinal.Limit.
Require Import ZF.Set.Ordinal.Omega.
Require Import ZF.Set.Ordinal.RecursionNOfClass.
Require Import ZF.Set.Ordinal.Succ.
Require Import ZF.Set.Relation.Eval.
Require Import ZF.Set.Relation.FunctionOn.

Module SORN := ZF.Set.Ordinal.RecursionNOfClass.

(* The recursion set associated with the sets f and  a.                         *)
(* In other words, the unique function g defined on N by the equations:         *)
(* (i)    g(0)      = a                                                         *)
(* (ii)   g(n+1) = f(g(n))                                                      *)
Definition recursion (f a:U) : U := SORN.recursion (toClass f) a.

(* The recursion set of f and a is a function defined on N.                     *)
Proposition IsFunctionOn : forall (f a:U),
  FunctionOn (recursion f a) :N.
Proof.
  intros f. apply SORN.IsFunctionOn.
Qed.

(* The recursion set of f and a has initial value a.                            *)
Proposition WhenZero : forall (f a:U),
  (recursion f a)!:0: = a.
Proof.
  intros f. apply SORN.WhenZero.
Qed.

(* The recursion set satisfies the equation g(n+1) = f(g(n)).                   *)
Proposition WhenSucc : forall (f a n:U),
  n :< :N                                            ->
  (recursion f a)!(succ n)  = f!((recursion f a)!n).
Proof.
  intros f. apply SORN.WhenSucc.
Qed.

(* The recursion set of f a is the unique function g defined on N such that     *)
(* g(0) = a and g(n+1) = f(g(n)) for all n.                                     *)
Proposition IsUnique : forall (f g a:U),
  FunctionOn g :N                               ->
  g!:0: = a                                     ->
  (forall n, n :< :N -> g!(succ n) = f!(g!n))   ->
  g = recursion f a.
Proof.
  intros f g a. apply SORN.IsUnique.
Qed.
