Require Import ZF.Class.Diff.
Require Import ZF.Class.Equiv.
Require Import ZF.Class.Incl.
Require Import ZF.Class.Proper.
Require Import ZF.Class.Relation.Converse.
Require Import ZF.Class.Relation.FunctionOn.
Require Import ZF.Class.Relation.OneToOne.
Require Import ZF.Class.Relation.Range.
Require Import ZF.Set.Core.
Require Import ZF.Set.Ordinal.Core.
Require Import ZF.Set.OrdPair.
Require Import ZF.Set.Relation.EvalOfClass.
Require Import ZF.Set.Relation.ImageByClass.

Proposition WhenFreshValue : forall (F A:Class),
  FunctionOn F Ordinal                                 ->
  (forall a, Ordinal a -> (A :\: toClass F:[a]:) F!a)  ->
  range F :<=: A                                       /\
  OneToOne F                                           /\
  Proper A.
Proof.
  intros F A H1 H2. split.
  - intros b H3. apply (FunctionOn.RangeCharac F Ordinal) in H3. 2: assumption.
    destruct H3 as [a [H3 H4]]. subst. apply H2. assumption.
  - split.
    +
Admitted.
