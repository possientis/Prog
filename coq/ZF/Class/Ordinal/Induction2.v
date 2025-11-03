Require Import ZF.Class.Equiv.
Require Import ZF.Class.Ordinal.Core.
Require Import ZF.Class.Ordinal.Induction.
Require Import ZF.Set.Core.
Require Import ZF.Set.Empty.
Require Import ZF.Set.Foundation.
Require Import ZF.Set.Incl.
Require Import ZF.Set.Ordinal.Core.
Require Import ZF.Set.Ordinal.Limit.
Require Import ZF.Set.Ordinal.Succ.
Require Import ZF.Set.Union.

Module COC := ZF.Class.Ordinal.Core.
Module SOC := ZF.Set.Ordinal.Core.

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

(* ERROR: see page 58 what is claimed to be needed to prove for (c) is too      *)
(* strong (and there is also a typo '/\ phi(beta)' should be '-> phi (beta)').  *)
(* The book forgets to have 'b <= a' in last hypothesis of proposition below.   *)
Proposition Induction2' : forall (A:Class) (b:U),
  On b                                                                    ->
  A b                                                                     ->
  (forall a, On a -> b :<=: a -> A a -> A (succ a))                       ->
  (forall a,
    Limit a                               ->
    b :<=: a                              ->
    (forall x, b :<=: x -> x :< a -> A x) ->
    A a                                    )                              ->
  forall a, On a -> b :<=: a -> A a.
Proof.
  intros A b H1 H3 H4 H5.
  remember (fun a => a :< b \/ A a) as B eqn:H6.
  assert (forall a, On a -> B a) as H7. {
    apply Induction2.
    - rewrite H6. assert (:0: :<=: b) as H7. { apply SOC.IsIncl. assumption. }
      apply SOC.InclIsEqualOrElem in H7. 3: assumption.
      + destruct H7 as [H7|H7]. 2: { left. assumption. }
        right. subst. assumption.
      + apply SOC.ZeroIsOrdinal.
    - rewrite H6. intros a H7 H8.
      assert (On (succ a)) as G1. { apply Succ.IsOrdinal. assumption. }
      destruct H8 as [H8|H8].
      + apply Succ.ElemIsIncl in H8; try assumption.
        apply Core.InclIsEqualOrElem in H8; try assumption.
        destruct H8 as [H8|H8].
        * right. rewrite H8. assumption.
        * left. assumption.
      + assert (succ a = b \/ succ a :< b \/ b :< succ a) as H9. {
          apply Core.IsTotal; assumption. }
        destruct H9 as [H9|[H9|H9]].
        * right. rewrite H9. assumption.
        * left. assumption.
        * apply Succ.ElemIsIncl in H9; try assumption.
          apply Succ.InclCompatRev in H9; try assumption.
          right. apply H4; assumption.
    - rewrite H6. intros a H7 H8.
      assert (On a) as G1. { apply H7. }
      assert (a :< b \/ b :<=: a) as H9. { apply Core.ElemOrIncl; assumption. }
      destruct H9 as [H9|H9]. 1: { left. assumption. }
      right. apply H5; try assumption. intros x H10 H11.
      assert (x :< b \/ A x) as H12. { apply H8. assumption. }
      destruct H12 as [H12|H12]. 2: assumption.
      exfalso. apply NoElemLoop1 with x. apply H10. assumption. }
  rewrite H6 in H7. intros a H8 H9.
  apply H7 in H8. destruct H8 as [H8|H8]. 2: assumption.
  exfalso. apply NoElemLoop1 with a. apply H9. assumption.
Qed.

