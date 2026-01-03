Require Import ZF.Class.Equiv.
Require Import ZF.Class.Ordinal.OrdFun.
Require Import ZF.Class.Ordinal.Sum.
Require Import ZF.Class.Relation.Domain.
Require Import ZF.Class.Relation.ToFun.
Require Import ZF.Set.Core.
Require Import ZF.Set.Empty.
Require Import ZF.Set.Ordinal.Core.
Require Import ZF.Set.Ordinal.Limit.
Require Import ZF.Set.Ordinal.Plus.
Require Import ZF.Set.Ordinal.Succ.
Require Import ZF.Set.Relation.EvalOfClass.
Require Import ZF.Set.UnionGenOfClass.

Require Import ZF.Notation.Eval.

Require Import ZF.Notation.Sum.
Export ZF.Notation.Sum.

Module COS := ZF.Class.Ordinal.Sum.
Module SUG := ZF.Set.UnionGenOfClass.

Definition sum (a:U) (F:Class) : U := (COS.sum F)!a.

(* Notation ":sum:_{a} F" := (sum a F)                                          *)
Global Instance SetClassSum : Sum U Class U := { sum := sum }.

Proposition WhenZero : forall (F:Class), :sum:_{:0:} F = :0:.
Proof.
  apply COS.WhenZero.
Qed.

Proposition WhenSucc : forall (F:Class) (a:U), Ordinal a ->
  :sum:_{succ a} F = :sum:_{a} F :+: F!a.
Proof.
  apply COS.WhenSucc.
Qed.

Proposition WhenLimit : forall (F:Class) (a:U), Limit a ->
  :sum:_{a} F = :\/:_{a} :[fun b => :sum:_{b} F]:.
Proof.
  intros F a H1.
  assert (:\/:_{a} (:[fun b => :sum:_{b} F]:) = :\/:_{a} (COS.sum F)) as H2. {
    apply SUG.EtaReduce. }
  rewrite H2. apply COS.WhenLimit. assumption.
Qed.

Proposition IsOrdinal : forall (F:Class) (a:U),
  OrdFun F                          ->
  Ordinal a                         ->
  (forall x, x :< a -> domain F x)  ->
  Ordinal (:sum:_{a} F).
Proof.
  apply COS.IsOrdinal.
Qed.
