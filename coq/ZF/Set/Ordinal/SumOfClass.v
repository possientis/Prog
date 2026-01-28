Require Import ZF.Class.Incl.
Require Import ZF.Class.Equiv.
Require Import ZF.Class.Ordinal.ShiftL.
Require Import ZF.Class.Ordinal.ShiftR.
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
  Ordinal a                           ->
  (forall x, x :< a -> Ordinal F!x)   ->
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
  Functional F                                        ->
  n :< :N                                             ->
  (forall i, i :< succ n -> domain F i)               ->
  (forall i, i :< succ n -> Ordinal F!i)              ->
  :sum:_{succ n} F = F!:0: :+: :sum:_{n} (shiftL F).
Proof.
  intros F n H1. revert n.
  assert (Ordinal :0:) as G1. { apply Core.ZeroIsOrdinal. }
  remember (fun n =>
    (forall i, i :< succ n -> domain F i)  ->
    (forall i, i :< succ n -> Ordinal F!i) ->
    :sum:_{succ n} F = F!:0: :+: :sum:_{n} (shiftL F)) as A eqn:H2.
  assert (forall n, n :< :N -> A n) as H3. {
    apply Omega.Induction; rewrite H2.
    - intros H3 H4.
      rewrite WhenSucc, WhenZero, Plus.WhenZeroL, WhenZero, Plus.WhenZeroR.
      3: assumption. 1: reflexivity. apply H4. apply Succ.IsIn.
    - intros n H3 IH H4 H5.
      assert (Ordinal n) as G2. { apply Omega.HasOrdinalElem. assumption. }
      assert (Ordinal (succ n)) as G3. { apply Succ.IsOrdinal. assumption. }
      rewrite WhenSucc, IH, WhenSucc, ShiftL.Eval; try assumption.
      + apply Plus.Assoc.
        * apply H5. apply Succ.HasZero; assumption.
        * apply IsOrdinal. 1: assumption.
          intros i H6.
          assert (Ordinal i) as G4. { apply SOC.IsOrdinal with n; assumption. }
          assert (Ordinal (succ i)) as G5. { apply Succ.IsOrdinal. assumption. }
          rewrite ShiftL.Eval. 2: assumption.
         { apply H5, Succ.ElemCompat; try assumption.
            apply SOC.ElemElemTran with n; try assumption.
            apply Succ.IsIn. }
         { apply H4, Succ.ElemCompat; try assumption.
            apply SOC.ElemElemTran with n; try assumption.
            apply Succ.IsIn. }
        * apply H5, Succ.IsIn.
      + apply H4, Succ.IsIn.
      + intros i H6. apply H4. apply Succ.IsIncl. assumption.
      + intros i H6. apply H5. apply Succ.IsIncl. assumption. }
  rewrite H2 in H3. assumption.
Qed.

Proposition ShiftR : forall (F:Class) (a n:U),
  Functional F                                        ->
  Ordinal a                                           ->
  n :< :N                                             ->
  (forall i, i :< n -> domain F i)                    ->
  (forall i, i :< n -> Ordinal F!i)                   ->
  :sum:_{succ n} (shiftR a F) = a :+: :sum:_{n} F.
Proof.
  intros F a n H1 H2. revert n.
  assert (Ordinal :0:) as G1. { apply Core.ZeroIsOrdinal. }
  remember (fun n =>
    (forall i, i :< n -> domain F i)                ->
    (forall i, i :< n -> Ordinal F!i)               ->
    :sum:_{succ n} (shiftR a F) = a :+: :sum:_{n} F) as A eqn:H3.
  assert (forall n, n :< :N -> A n) as H4. {
    apply Omega.Induction; rewrite H3.
    - intros H4 H5.
      rewrite WhenSucc, WhenZero, WhenZero, ShiftR.EvalZero; try assumption.
      rewrite Plus.WhenZeroL, Plus.WhenZeroR. 2: assumption. reflexivity.
    - intros n H4 IH H5 H6.
      assert (Ordinal n) as G2. { apply Omega.HasOrdinalElem. assumption. }
      assert (Ordinal (succ n)) as G3. { apply Succ.IsOrdinal. assumption. }
      rewrite WhenSucc. 2: assumption.
      assert (:sum:_{ succ n} (shiftR a F) = a :+: :sum:_{ n} F) as H7. {
        apply IH.
        - intros i H7. apply H5, Succ.IsIncl. assumption.
        - intros i H7. apply H6, Succ.IsIncl. assumption. }
      assert (:sum:_{ succ n} (shiftR a F) :+: (shiftR a F)!(succ n)
        = a :+: :sum:_{ succ n} F) as X. 2: apply X. (* rewrite failure *)
      assert (Ordinal (:sum:_{n} F)) as H8. {
        apply IsOrdinal. 1: assumption.
        intros i H8. apply H6, Succ.IsIncl. assumption. }
      rewrite H7, ShiftR.EvalSucc, Plus.Assoc, <- WhenSucc;
      try assumption. 1: reflexivity.
      + apply H6, Succ.IsIn.
      + apply H5, Succ.IsIn. }
  rewrite H3 in H4. assumption.
Qed.
