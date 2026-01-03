Require Import ZF.Class.Equiv.
Require Import ZF.Class.Incl.
Require Import ZF.Class.Ordinal.Core.
Require Import ZF.Class.Ordinal.Induction2.
Require Import ZF.Class.Ordinal.Recursion2.
Require Import ZF.Class.Relation.Domain.
Require Import ZF.Class.Relation.Function.
Require Import ZF.Class.Relation.Range.
Require Import ZF.Set.Core.
Require Import ZF.Set.Empty.
Require Import ZF.Set.Ordinal.Limit.
Require Import ZF.Set.Ordinal.Succ.
Require Import ZF.Set.Ordinal.UnionGenOfClass.
Require Import ZF.Set.OrdPair.
Require Import ZF.Set.Relation.EvalOfClass.


Module COC := ZF.Class.Ordinal.Core.
Module CRF := ZF.Class.Relation.Function.

(* An ordinal function is a function with ordinal domain and ordinal values.    *)
Definition OrdFun (F:Class) : Prop
  := Function F /\ Ordinal (domain F) /\ range F :<=: On.

Proposition FromRecursion : forall (F:Class) (a:U),
  On a                      ->
  OrdFun F                  ->
  domain F :~: On           ->
  OrdFun (Recursion F a).
Proof.
  intros F a H1 [H2 [_ H3]] H4.
  assert (domain (Recursion F a) :~: On) as H5. { apply Recursion2.IsFunctionOn. }
  split.
  - apply Recursion2.IsFunctionOn.
  - split.
    + apply Core.EquivCompat with On. apply Equiv.Sym.
      1: assumption. apply Core.OnIsOrdinal.
    + assert (forall x, On x -> On (Recursion F a)!x) as H6. {
        apply Induction2.
        - rewrite Recursion2.WhenZero. assumption.
        - intros b H6 H7. rewrite Recursion2.WhenSucc. 2: assumption.
          apply H3. apply CRF.IsInRange. 1: assumption. apply H4. assumption.
        - intros b H6 H7. rewrite Recursion2.WhenLimit. 2: assumption.
          apply UnionGenOfClass.IsOrdinal. assumption. }
      intros y H7. destruct H7 as [x H7].
      assert (On x) as H8. { apply H5. exists y. assumption. }
      apply CRF.EvalCharac in H7.
      * rewrite <- H7. apply H6. assumption.
      * apply Recursion2.IsFunctionOn.
      * apply H5. assumption.
Qed.

Proposition WhenInDomain : forall (F:Class) (a:U), OrdFun F ->
  domain F a -> On a.
Proof.
  intros F a [H1 [H2 H3]] H4.
  apply COC.IsOrdinal with (domain F); assumption.
Qed.

Proposition IsOrdinal : forall (F:Class) (a:U), OrdFun F ->
  domain F a -> On (F!a).
Proof.
  intros F a [H1 [H2 H3]] H4. apply H3. apply CRF.IsInRange; assumption.
Qed.
