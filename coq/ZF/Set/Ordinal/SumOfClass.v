Require Import ZF.Class.Equiv.
Require Import ZF.Class.Ordinal.OrdFun.
Require Import ZF.Class.Ordinal.ShiftL.
Require Import ZF.Class.Ordinal.Sum.
Require Import ZF.Class.Relation.Domain.
Require Import ZF.Class.Relation.Functional.
Require Import ZF.Class.Relation.ToFun.
Require Import ZF.Set.Core.
Require Import ZF.Set.Empty.
Require Import ZF.Set.Ordinal.Core.
Require Import ZF.Set.Ordinal.Limit.
Require Import ZF.Set.Ordinal.Omega.
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

Proposition EqualCharac : forall (F G:Class) (a:U),
  Ordinal a                       ->
  (forall x, x :< a -> F!x = G!x) ->
  :sum:_{a} F = :sum:_{a} G.
Proof.
  apply COS.EqualCharac.
Qed.

Proposition EtaReduce : forall (F:Class) (a:U), Ordinal a ->
  :sum:_{a} (:[fun x => F!x]:) = :sum:_{a} F.
Proof.
  intros F a H1. apply EqualCharac. 1: assumption.
  intros x H2. apply ToFun.Eval.
Qed.

Proposition ShiftL : forall (F:Class) (n:U),
  OrdFun F                                            ->
  n :< :N                                             ->
  domain F n                                          ->
  :sum:_{succ n} F = F!:0: :+: :sum:_{n} (shiftL F).
Proof.
  intros F n H1. revert n.
  assert (Ordinal :0:) as G1. { apply Core.ZeroIsOrdinal. }
  assert (Functional F) as G2. { apply H1. }
  remember (fun n =>
    domain F n ->  :sum:_{succ n} F = F!:0: :+: :sum:_{n} (shiftL F)) as A eqn:H2.
  assert (forall n, n :< :N -> A n) as H3. {
    apply Omega.FiniteInduction'; rewrite H2.
    - intros H3.
      rewrite WhenSucc, WhenZero, Plus.WhenZeroL, WhenZero, Plus.WhenZeroR.
      3: assumption. 1: reflexivity. apply OrdFun.IsOrdinal; assumption.
    - intros n H3 IH H4.
      assert (Ordinal n) as G3. { apply Omega.HasOrdinalElem. assumption. }
      assert (Ordinal (succ n)) as G4. { apply Succ.IsOrdinal. assumption. }
      rewrite WhenSucc, IH, WhenSucc, ShiftL.Eval; try assumption.
      + apply Plus.Assoc.
        * apply OrdFun.IsOrdinal. 1: assumption.
          apply OrdFun.InDomain with (succ n); try assumption.
          apply Succ.HasZero. assumption.
        * apply IsOrdinal. 2: assumption.
          { apply ShiftL.IsOrdFun. assumption. }
          { intros i H5.
            apply ShiftL.DomainOf.
            apply OrdFun.InDomain with (succ n); try assumption.
            apply Succ.ElemCompat; try assumption.
            apply Core.IsOrdinal with n; assumption. }
        * apply OrdFun.IsOrdinal; assumption.
      + apply OrdFun.InDomain with (succ n); try assumption. apply Succ.IsIn. }
  rewrite H2 in H3. assumption.
Qed.
