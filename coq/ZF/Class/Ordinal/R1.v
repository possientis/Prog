Require Import ZF.Class.Equiv.
Require Import ZF.Class.Ordinal.Core.
Require Import ZF.Class.Ordinal.Induction2.
Require Import ZF.Class.Ordinal.Recursion2.
Require Import ZF.Class.Relation.ToFun.
Require Import ZF.Set.Core.
Require Import ZF.Set.Empty.
Require Import ZF.Set.Incl.
Require Import ZF.Set.Ordinal.Core.
Require Import ZF.Set.Ordinal.Limit.
Require Import ZF.Set.Ordinal.Succ.
Require Import ZF.Set.Ordinal.Super.
Require Import ZF.Set.Ordinal.Transitive.
Require Import ZF.Set.Power.
Require Import ZF.Set.Relation.EvalOfClass.
Require Import ZF.Set.UnionGenOfClass.

Require Import ZF.Notation.Eval.

Module CFO := ZF.Class.Relation.FunctionOn.

(* Function class needed to define the rank of a set.                           *)
Definition R1 : Class := Recursion :[fun a => :P(a)]: :0:.

Proposition IsFunctionOn : CFO.FunctionOn R1 On.
Proof.
  apply Recursion2.IsFunctionOn.
Qed.

Proposition WhenZero : R1!:0: = :0:.
Proof.
  apply Recursion2.WhenZero.
Qed.

Proposition WhenSucc : forall a, On a ->
  R1!(succ a) = :P(R1!a).
Proof.
  intros a H1.
  assert (R1!(succ a) = :[fun b => :P(b)]:!(R1!a)) as H2. {
    apply Recursion2.WhenSucc. assumption. }
  rewrite H2. apply ToFun.Eval.
Qed.

Proposition WhenLimit : forall (a:U), Limit a ->
  R1!a = :\/:_{a} R1.
Proof.
  intros a H1. apply Recursion2.WhenLimit. assumption.
Qed.

Proposition IsUnique : forall (G:Class),
  CFO.FunctionOn G On                       ->
  G!:0: = :0:                               ->
  (forall a, On a -> G!(succ a) = :P(G!a))  ->
  (forall a, Limit a -> G!a = :\/:_{a} G)   ->
  G :~: R1.
Proof.
  intros G H1 H2 H3. apply Recursion2.IsUnique; try assumption.
  intros b H4. symmetry. rewrite H3. 2: assumption. apply ToFun.Eval.
Qed.

Proposition IsSuper : forall (a:U), On a ->
  Super R1!a.
Proof.
  apply Induction2.Induction.
  - rewrite WhenZero. apply Super.WhenZero. reflexivity.
  - intros a H1 IH. rewrite WhenSucc. 2: assumption.
    apply Super.WhenPower. assumption.
  - intros a H1 IH. rewrite WhenLimit. 2: assumption.
    apply Super.WhenUnion. assumption.
Qed.

Proposition IsTransitive : forall (a:U), On a ->
  Transitive R1!a.
Proof.
  intros a H1. apply IsSuper. assumption.
Qed.

Proposition ElemSucc : forall (a:U), On a ->
  R1!a :< R1!(succ a).
Proof.
  intros a H1. rewrite WhenSucc. 2: assumption. apply Power.Charac, Incl.Refl.
Qed.

Proposition InclSucc : forall (a:U), On a ->
  R1!a :<=: R1!(succ a).
Proof.
  intros a H1 x H2.
  apply IsTransitive with R1!a. 2: assumption.
  - apply Succ.IsOrdinal. assumption.
  - apply ElemSucc. assumption.
Qed.

Proposition ElemCompat : forall (a b:U), On a -> On b ->
  a :< b -> R1!a :< R1!b.
Proof.
  intros a b H1. revert b.
  assert (On (succ a)) as G1. { apply Succ.IsOrdinal. assumption. }
  assert (forall b, On b -> succ a :<=: b -> R1!a :< R1!b) as H2. {
    apply Induction2.Induction'. 1: assumption.
    - apply ElemSucc. assumption.
    - intros b H2 H3 IH. apply InclSucc; assumption.
    - intros b H2 H3 IH. rewrite (WhenLimit b). 2: assumption.
      apply SUG.Charac. exists (succ a).
      assert (succ a :< b) as H4. {
        apply Limit.HasSucc. 1: assumption. apply H3, Succ.IsIn. }
      split. 1: assumption. apply ElemSucc. assumption. }
  intros b H3 H4. apply H2. 1: assumption.
  apply Succ.ElemIsIncl; assumption.
Qed.

Proposition ElemInclCompat : forall (a b:U), On a -> On b ->
  a :< b -> R1!a :<=: R1!b.
Proof.
  intros a b H1 H2 H3 x H4.
  apply IsTransitive with R1!a; try assumption.
  apply ElemCompat; assumption.
Qed.

