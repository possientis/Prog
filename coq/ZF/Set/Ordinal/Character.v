Require Import ZF.Class.Equiv.
Require Import ZF.Set.Core.
Require Import ZF.Set.Empty.
Require Import ZF.Set.Incl.
Require Import ZF.Set.Ordinal.Cofinal.
Require Import ZF.Set.Ordinal.Core.
Require Import ZF.Set.Ordinal.Inf.
Require Import ZF.Set.Ordinal.Limit.
Require Import ZF.Set.Ordinal.Natural.
Require Import ZF.Set.Ordinal.Omega.
Require Import ZF.Set.Ordinal.Succ.
Require Import ZF.Set.Specify.

(* The character of cofinality of the ordinal a.                                *)
Definition charac (a:U) : U := inf {{ x :< succ a | Cofinal a }}.

(* The character of cofinality of an ordinal is contained in the ordinal.       *)
Proposition IsIncl : forall (a:U), Ordinal a ->
  charac a :<=: a.
Proof.
(* Proof by Hermes + gpt 5.5                                                    *)
  intros a H1.
  (* The candidates are the ordinals below succ a cofinal with a.               *)
  remember {{ x :< succ a | Cofinal a }} as r eqn:Hr.
  assert (toClass r :<=: Ordinal) as H2. {
    intros x H2. rewrite Hr in H2. apply Specify.Charac in H2.
    destruct H2 as [H2 _]. apply Core.IsOrdinal with (succ a). 2: assumption.
    apply Succ.IsOrdinal. assumption. }
  assert (a :< r) as H3. {
    rewrite Hr. apply Specify.Charac. split.
    - apply Succ.IsIn.
    - apply Cofinal.Refl. assumption. }
  (* Since a is one of the candidates, their infimum is below a.                *)
  unfold charac. rewrite <- Hr. apply Inf.IsLowerBound; assumption.
Qed.

(* The character of cofinality of zero is zero.                                 *)
Proposition WhenZero : charac :0: = :0:.
Proof.
(* Proof by Hermes + gpt 5.5                                                    *)
  apply Empty.WhenIncl. apply IsIncl. apply Core.Zero.
Qed.

(* The character of cofinality of a successor ordinal is one.                   *)
Proposition WhenSucc : forall (a:U), Ordinal a ->
  charac (succ a) = :1:.
Proof.
(* Proof by Hermes + gpt 5.5                                                    *)
  intros a H1.
  (* The candidates are the ordinals below succ (succ a) cofinal with succ a.   *)
  remember {{ x :< succ (succ a) | Cofinal (succ a) }} as r eqn:Hr.
  assert (toClass r :<=: Ordinal) as H2. {
    intros x H2. rewrite Hr in H2. apply Specify.Charac in H2.
    destruct H2 as [H2 _]. apply Core.IsOrdinal with (succ (succ a)).
    2: assumption. apply Succ.IsOrdinal, Succ.IsOrdinal. assumption. }
  assert (:1: :< r) as H3. {
    assert (:1: :< succ (succ a)) as H3. {
      assert (Ordinal (succ a)) as H3. { apply Succ.IsOrdinal. assumption. }
      assert (:1: :<=: succ a) as H4. {
        apply Natural.HasZeroRev. 1: assumption. apply Succ.HasZero. assumption. }
      apply Core.InclElemTran with (succ a); try assumption.
      + apply Natural.OneIsOrdinal.
      + apply Succ.IsOrdinal. assumption.
      + apply Succ.IsIn. }
    assert (Cofinal (succ a) :1:) as H4. {
      apply Cofinal.WhenOne.
      - apply Natural.HasZeroRev.
        + apply Succ.IsOrdinal. assumption.
        + apply Succ.HasZero. assumption.
      - apply Succ.IsSuccessor. assumption. }
    rewrite Hr. apply Specify.Charac. split; assumption. }
  assert (charac (succ a) :<=: :1:) as H4. {
    unfold charac. rewrite <- Hr. apply Inf.IsLowerBound; assumption. }
  assert (:1: :<=: charac (succ a)) as H5. {
    assert (r <> :0:) as H5. { apply Empty.HasElem. exists :1:. assumption. }
    assert (forall x, x :< r -> :1: :<=: x) as H6. {
      intros x H6. rewrite Hr in H6. apply Specify.Charac in H6.
      destruct H6 as [H6 H7].
      assert (Ordinal x) as H8. {
        apply Core.IsOrdinal with (succ (succ a)). 2: assumption.
        apply Succ.IsOrdinal, Succ.IsOrdinal. assumption. }
      assert (x <> :0:) as H9. {
        intros H9. subst. apply Cofinal.WhenZero in H7.
        apply Succ.NotZero with a. assumption. }
      assert (:0: :< x) as H10. { apply Core.HasZero; assumption. }
      apply Natural.HasZeroRev; assumption. }
    unfold charac. rewrite <- Hr. apply Inf.IsLargest; assumption. }
  apply Incl.Double. split; assumption.
Qed.

(* The character of cofinality of omega is omega.                               *)
Proposition WhenOmega : charac :N = :N.
Proof.
(* Proof by Hermes + gpt 5.5                                                    *)
  (* The candidates are the ordinals below succ N cofinal with N.               *)
  remember {{ x :< succ :N | Cofinal :N }} as r eqn:Hr.
  assert (charac :N :<=: :N) as H1. { apply IsIncl. apply Omega.IsOrdinal. }
  assert (toClass r :<=: Ordinal) as H2. {
    intros x H2. rewrite Hr in H2. apply Specify.Charac in H2.
    destruct H2 as [H2 _]. apply Core.IsOrdinal with (succ :N). 2: assumption.
    apply Succ.IsOrdinal. apply Omega.IsOrdinal. }
  assert (:N :< r) as H3. {
    rewrite Hr. apply Specify.Charac. split.
    - apply Succ.IsIn.
    - apply Cofinal.Refl. apply Omega.IsOrdinal. }
  assert (:N :<=: charac :N) as H4. {
    assert (r <> :0:) as H4. { apply Empty.HasElem. exists :N. assumption. }
    assert (forall x, x :< r -> :N :<=: x) as H5. {
      intros x H5. rewrite Hr in H5. apply Specify.Charac in H5.
      destruct H5 as [H5 H6].
      assert (Ordinal x) as H7. { apply H2. rewrite Hr. apply Specify.Charac.
        split; assumption. }
      assert (Limit x) as H8. {
        assert (Limit :N <-> Limit x) as H8. {
          apply Cofinal.LimitCompat; try assumption. apply Omega.IsOrdinal. }
        apply H8. apply Omega.IsLimit. }
      apply Omega.IsInclLimit. assumption. }
    unfold charac. rewrite <- Hr. apply Inf.IsLargest; assumption. }
  apply Incl.Double. split; assumption.
Qed.
