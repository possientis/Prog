Require Import ZF.Class.Equiv.
Require Import ZF.Class.Ordinal.Core.
Require Import ZF.Class.Ordinal.Induction2.
Require Import ZF.Class.Ordinal.Recursion2.
Require Import ZF.Class.Relation.Fun.From.
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
Module COC := ZF.Class.Ordinal.Core.

(* The cumulative hierarchy assigns a rank-initial segment to each ordinal.     *)
(* (i)   VH(0)      = 0                                                         *)
(* (ii)  VH(succ a) = P(VH(a))                                                  *)
(* (iii) VH(a)      = \/_{x :< a} VH(x), when a is a limit ordinal              *)
Definition VH : Class := Recursion :[fun a => :P(a)]: :0:.

(* VH is a function class defined on the class of ordinals.                     *)
Proposition IsFunctionOn : CFO.FunctionOn VH On.
Proof.
  apply Recursion2.IsFunctionOn.
Qed.

(* VH evaluated at 0 is 0.                                                      *)
Proposition WhenZero : VH!:0: = :0:.
Proof.
  apply Recursion2.WhenZero.
Qed.

(* VH evaluated at succ a is the power set of VH!a.                             *)
Proposition WhenSucc : forall a, On a ->
  VH!(succ a) = :P(VH!a).
Proof.
  intros a H1.
  assert (VH!(succ a) = :[fun b => :P(b)]:!(VH!a)) as H2. {
    apply Recursion2.WhenSucc. assumption. }
  rewrite H2. apply From.Eval.
Qed.

(* VH evaluated at a limit ordinal a is the union of VH restricted to a.        *)
Proposition WhenLimit : forall (a:U), Limit a ->
  VH!a = :\/:_{a} VH.
Proof.
  intros a H1. apply Recursion2.WhenLimit. assumption.
Qed.

(* VH is the unique function satisfying the three recursion equations.          *)
Proposition IsUnique : forall (G:Class),
  CFO.FunctionOn G On                       ->
  G!:0: = :0:                               ->
  (forall a, On a -> G!(succ a) = :P(G!a))  ->
  (forall a, Limit a -> G!a = :\/:_{a} G)   ->
  G :~: VH.
Proof.
  intros G H1 H2 H3. apply Recursion2.IsUnique; try assumption.
  intros b H4. symmetry. rewrite H3. 2: assumption. apply From.Eval.
Qed.

(* For every ordinal a, VH(a) is a super-transitive set.                        *)
Proposition IsSuper : forall (a:U), On a ->
  Super VH!a.
Proof.
  apply Induction2.Induction.
  - rewrite WhenZero. apply Super.WhenZero. reflexivity.
  - intros a H1 IH. rewrite WhenSucc. 2: assumption.
    apply Super.WhenPower. assumption.
  - intros a H1 IH. rewrite WhenLimit. 2: assumption.
    apply Super.WhenUnion. assumption.
Qed.

(* For every ordinal a, VH(a) is a transitive set.                              *)
Proposition IsTransitive : forall (a:U), On a ->
  Transitive VH!a.
Proof.
  intros a H1. apply IsSuper. assumption.
Qed.

(* VH(a) is a member of VH(succ a) for every ordinal a.                         *)
Proposition ElemSucc : forall (a:U), On a ->
  VH!a :< VH!(succ a).
Proof.
  intros a H1. rewrite WhenSucc. 2: assumption. apply Power.Charac, Incl.Refl.
Qed.

(* VH(a) is a subset of  VH(succ a) for every ordinal a.                        *)
Proposition InclSucc : forall (a:U), On a ->
  VH!a :<=: VH!(succ a).
Proof.
  intros a H1 x H2.
  apply IsTransitive with VH!a. 2: assumption.
  - apply Succ.IsOrdinal. assumption.
  - apply ElemSucc. assumption.
Qed.

(* VH is strictly increasing: a :< b implies VH(a) :< VH(b).                    *)
Proposition ElemCompat : forall (a b:U), On a -> On b ->
  a :< b -> VH!a :< VH!b.
Proof.
  intros a b H1. revert b.
  assert (On (succ a)) as G1. { apply Succ.IsOrdinal. assumption. }
  assert (forall b, On b -> succ a :<=: b -> VH!a :< VH!b) as H2. {
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

(* VH is increasing: a :<=: b implies VH(a) :<=: VH(b).                         *)
Proposition InclCompat : forall (a b:U), On a -> On b ->
  a :<=: b -> VH!a :<=: VH!b.
Proof.
  intros a b H1 H2 H3.
  apply Core.EqualOrElem in H3; try assumption.
  destruct H3 as [H3|H3].
  - subst. apply Incl.Refl.
  - intros x H4.
    apply IsTransitive with VH!a; try assumption.
    apply ElemCompat; assumption.
Qed.
