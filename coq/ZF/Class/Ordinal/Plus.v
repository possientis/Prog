Require Import ZF.Class.Equiv.
Require Import ZF.Class.Ordinal.Core.
Require Import ZF.Class.Ordinal.Induction2.
Require Import ZF.Class.Ordinal.Recursion2.
Require Import ZF.Class.Relation.FunctionOn.
Require Import ZF.Class.Relation.ToFun.
Require Import ZF.Set.Core.
Require Import ZF.Set.Empty.
Require Import ZF.Set.Ordinal.Limit.
Require Import ZF.Set.Ordinal.Succ.
Require Import ZF.Set.Ordinal.UnionGenOfClass.
Require Import ZF.Set.Relation.EvalOfClass.
Require Import ZF.Set.Relation.FunctionOn.
Require Import ZF.Set.Relation.RestrictOfClass.
Require Import ZF.Set.UnionGenOfClass.

Require Import ZF.Notation.Eval.

Module CFO := ZF.Class.Relation.FunctionOn.
Module SFO := ZF.Set.Relation.FunctionOn.

(* The function class (a + .) when a is an ordinal.                             *)
Definition Plus (a:U) : Class := Recursion :[fun b => succ b]: a.

(* Plus a is a function class defined on the class of ordinals.                 *)
Proposition IsFunctionOn : forall (a:U), CFO.FunctionOn (Plus a) On.
Proof.
  intros a. apply Recursion2.IsFunctionOn.
Qed.

(* Plus a evaluated at 0 is a.                                                  *)
Proposition WhenZero : forall (a:U), (Plus a)!:0: = a.
Proof.
  intros a. apply Recursion2.WhenZero.
Qed.

(* a + (succ b) = succ (a + b).                                                 *)
Proposition WhenSucc : forall (a b:U), On b ->
  (Plus a)!(succ b) = succ ((Plus a)!b).
Proof.
  intros a b H1.
  assert ((Plus a)!(succ b) = :[fun b => succ b]:!((Plus a)!b)) as H2. {
    apply Recursion2.WhenSucc. assumption. }
  rewrite H2. apply ToFun.Eval.
Qed.

(* a + b = \/_{c :< b} a + c when b is a limit ordinal.                         *)
Proposition WhenLimit : forall (a b:U), Limit b ->
  (Plus a)!b = :\/:_{b} (Plus a).
Proof.
  intros a b H1. apply Recursion2.WhenLimit. assumption.
Qed.

Proposition IsUnique : forall (G:Class) (a:U),
  CFO.FunctionOn G On                         ->
  G!:0: = a                                   ->
  (forall b, On b -> G!(succ b) = succ (G!b)) ->
  (forall b, Limit b -> G!b = :\/:_{b} G)     ->
  G :~: Plus a.
Proof.
  intros G a H1 H2 H3. apply Recursion2.IsUnique; try assumption.
  intros b H4. symmetry. rewrite H3. 2: assumption. apply ToFun.Eval.
Qed.

Proposition RestrictIsFunctionOn : forall (a b:U), On b ->
  SFO.FunctionOn ((Plus a) :|: b) b.
Proof.
  intros a b. apply Recursion2.RestrictIsFunctionOn.
Qed.
