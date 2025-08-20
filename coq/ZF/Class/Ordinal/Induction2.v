Require Import ZF.Class.Equiv.
Require Import ZF.Class.Ordinal.Core.
Require Import ZF.Class.Ordinal.Induction.
Require Import ZF.Set.Core.
Require Import ZF.Set.Empty.
Require Import ZF.Set.Ordinal.Limit.
Require Import ZF.Set.Ordinal.Succ.
Require Import ZF.Set.Union.

Proposition Induction2 : forall (A:Class),
  A :0:                                                     ->
  (forall a, On a    -> A a -> A (succ a))                  ->
  (forall a, Limit a -> (forall x, x :< a -> A x) -> A a)   ->
  forall a, On a -> A a.
Proof.
  intros A H1 H2 H3. apply Induction'. intros a H4 H5.
  assert (a = :0: \/ a = succ :U(a) \/ Limit a) as H6. {
    apply Limit.ThreeWay. assumption. }
  destruct H6 as [H6|[H6|H6]].
  - rewrite H6. assumption.
  - rewrite H6. apply H2.
    + apply Succ.IsOrdinalRev. rewrite <- H6. assumption.
    + remember :U(a) as b eqn:H7. apply H5. rewrite H6, H7. apply Succ.IsIn.
  - apply H3; assumption.
Qed.
