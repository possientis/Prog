Require Import ZF.Class.Complement.
Require Import ZF.Class.Diff.
Require Import ZF.Class.Equiv.
Require Import ZF.Class.Incl.
Require Import ZF.Class.Ordinal.Core.
Require Import ZF.Class.Proper.
Require Import ZF.Class.Relation.Converse.
Require Import ZF.Class.Relation.Domain.
Require Import ZF.Class.Relation.FunctionOn.
Require Import ZF.Class.Relation.OneToOne.
Require Import ZF.Class.Relation.Range.
Require Import ZF.Class.Small.
Require Import ZF.Set.Core.
Require Import ZF.Set.Ordinal.Core.
Require Import ZF.Set.OrdPair.
Require Import ZF.Set.Relation.EvalOfClass.
Require Import ZF.Set.Relation.ImageByClass.

Module COC := ZF.Class.Ordinal.Core.
Module SOC := ZF.Set.Ordinal.Core.


Proposition WhenFreshValue : forall (F A:Class),
  FunctionOn F On                                 ->
  (forall a, On a -> (A :\: toClass F:[a]:) F!a)  ->
  range F :<=: A                                  /\
  OneToOne F                                      /\
  Proper A.
Proof.
  intros F A H1 H2.
  assert (range F :<=: A) as H3. {
    intros b H3. apply (FunctionOn.RangeCharac F On) in H3. 2: assumption.
    destruct H3 as [a [H3 H4]]. subst. apply H2. assumption. }
  assert (OneToOne F) as H4. {
    apply FunctionOn.IsOneToOne with On. 1: assumption.
    intros a b H4 H5 H6.
    assert (a = b \/ a :< b \/ b :< a) as H7. {
      apply SOC.OrdinalTotal; assumption. }
    destruct H7 as [H7|[H7|H7]]. 1: assumption.
    - exfalso. specialize (H2 b H5). rewrite <- H6 in H2.
      destruct H2 as [_ H2]. apply H2.
      apply ImageByClass.IsIn; try apply H1; assumption.
    - exfalso. specialize (H2 a H4). rewrite H6 in H2.
      destruct H2 as [_ H2]. apply H2.
      apply ImageByClass.IsIn; try apply H1; assumption. }
  assert (Proper A) as H5. {
    intros H5.
    assert (Small (range F)) as H6. {
      apply Bounded.WhenSmaller with A; assumption. }
    assert (Small On) as H7. {
      apply Small.EquivCompat with (domain F). 1: apply H1.
      apply Function.DomainIsSmall; assumption. }
    revert H7. apply COC.OnIsProper. }
  split. 1: assumption. split; assumption.
Qed.
