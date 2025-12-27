Require Import ZF.Class.Equiv.
Require Import ZF.Class.Ordinal.Core.
Require Import ZF.Class.Ordinal.Recursion2.
Require Import ZF.Class.Relation.FunctionOn.
Require Import ZF.Class.Relation.ToFun.
Require Import ZF.Set.Core.
Require Import ZF.Set.Empty.
Require Import ZF.Set.Ordinal.Limit.
Require Import ZF.Set.Ordinal.Plus.
Require Import ZF.Set.Ordinal.Succ.
Require Import ZF.Set.Relation.EvalOfClass.
Require Import ZF.Set.Relation.FunctionOn.
Require Import ZF.Set.Relation.RestrictOfClass.
Require Import ZF.Set.UnionGenOfClass.

Require Import ZF.Notation.Eval.

Module CFO := ZF.Class.Relation.FunctionOn.
Module SFO := ZF.Set.Relation.FunctionOn.

(* The function class (a * .) when a is an ordinal.                             *)
Definition Mult (a:U) : Class := Recursion :[fun b => b :+: a]: :0:.

(* Plus a is a function class defined on the class of ordinals.                 *)
Proposition IsFunctionOn : forall (a:U), CFO.FunctionOn (Mult a) On.
Proof.
  intros a. apply Recursion2.IsFunctionOn.
Qed.

(* Mutl a evaluated at 0 is 0.                                                  *)
Proposition WhenZero : forall (a:U), (Mult a)!:0: = :0:.
Proof.
  intros a. apply Recursion2.WhenZero.
Qed.

(* a * (succ b) = a * b + a                                                     *)
Proposition WhenSucc : forall (a b:U), On b ->
  (Mult a)!(succ b) = (Mult a)!b :+: a.
Proof.
  intros a b H1.
  assert ((Mult a)!(succ b) = :[fun b => b :+: a]:!((Mult a)!b)) as H2. {
    apply Recursion2.WhenSucc. assumption. }
    rewrite H2.
    apply (ToFun.Eval (fun b => b :+: a)).
Qed.

(* a * b = \/_{c :< b} a * c when b is a limit ordinal.                         *)
Proposition WhenLimit : forall (a b:U), Limit b ->
  (Mult a)!b = :\/:_{b} (Mult a).
Proof.
  intros a b H1. apply Recursion2.WhenLimit. assumption.
Qed.

Proposition IsUnique : forall (G:Class) (a:U),
  CFO.FunctionOn G On                         ->
  G!:0: = :0:                                 ->
  (forall b, On b -> G!(succ b) = G!b :+: a)  ->
  (forall b, Limit b -> G!b = :\/:_{b} G)     ->
  G :~: Mult a.
Proof.
  intros G a H1 H2 H3. apply Recursion2.IsUnique; try assumption.
  intros b H4. symmetry. rewrite H3. 2: assumption.
  apply (ToFun.Eval (fun b => b :+: a)).
Qed.

Proposition RestrictIsFunctionOn : forall (a b:U), On b ->
  SFO.FunctionOn ((Mult a) :|: b) b.
Proof.
  intros a b. apply Recursion2.RestrictIsFunctionOn.
Qed.
