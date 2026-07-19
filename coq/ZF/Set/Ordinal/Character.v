Require Import ZF.Class.Equiv.
Require Import ZF.Set.Cardinal.Core.
Require Import ZF.Set.Cardinal.Equiv.
Require Import ZF.Set.Core.
Require Import ZF.Set.Empty.
Require Import ZF.Set.Foundation.
Require Import ZF.Set.Incl.
Require Import ZF.Set.Ordinal.Cofinal.
Require Import ZF.Set.Ordinal.Core.
Require Import ZF.Set.Ordinal.Inf.
Require Import ZF.Set.Ordinal.Limit.
Require Import ZF.Set.Ordinal.Natural.
Require Import ZF.Set.Ordinal.Omega.
Require Import ZF.Set.Ordinal.Succ.
Require Import ZF.Set.Specify.

Module SCC := ZF.Set.Cardinal.Core.
Module SCE := ZF.Set.Cardinal.Equiv.
Module SOC := ZF.Set.Ordinal.Core.

(* The character of cofinality of the ordinal a.                                *)
Definition charac (a:U) : U := inf {{ x :< succ a | Cofinal a }}.

(* The character of cofinality is an ordinal.                                   *)
Proposition IsOrdinal : forall (a:U), Ordinal (charac a).
Proof.
(* Proof by Hermes + gpt 5.5                                                    *)
  intros a. apply Inf.IsOrdinal.
Qed.

(* The character of cofinality is below every cofinal ordinal.                  *)
Proposition IsLowerBound : forall (a b:U),
  Ordinal a         ->
  Ordinal b         ->
  Cofinal a b       ->
  charac a :<=: b.
Proof.
(* Proof by Hermes + gpt 5.5                                                    *)
  intros a b H1 H2 H3.
  (* The candidate set consists of ordinals below succ a cofinal with a.        *)
  remember {{ x :< succ a | Cofinal a }} as r eqn:Hr.
  assert (toClass r :<=: Ordinal) as H4. {
    intros x H4. rewrite Hr in H4. apply Specify.Charac in H4.
    destruct H4 as [H4 _]. apply SOC.IsOrdinal with (succ a). 2: assumption.
    apply Succ.IsOrdinal. assumption. }
  assert (b :< r) as H5. {
    assert (b :<=: a) as H5. { apply H3. }
    assert (b :< succ a) as H6. {
      apply SOC.InclElemTran with a; try assumption.
      - apply Succ.IsOrdinal. assumption.
      - apply Succ.IsIn. }
    rewrite Hr. apply Specify.Charac. split; assumption. }
  (* The infimum of all candidates is below this particular candidate.          *)
  unfold charac. rewrite <- Hr. apply Inf.IsLowerBound; assumption.
Qed.

(* The character of cofinality contains every common lower bound.               *)
Proposition IsLargest : forall (a b:U),
  Ordinal a                                         ->
  Ordinal b                                         ->
  (forall c, Ordinal c -> Cofinal a c -> b :<=: c)  ->
  b :<=: charac a.
Proof.
(* Proof by Hermes + gpt 5.5                                                    *)
  intros a b H1 H2 H3.
  (* The candidate set is non-empty because a is cofinal with itself.           *)
  remember {{ x :< succ a | Cofinal a }} as r eqn:Hr.
  assert (toClass r :<=: Ordinal) as H4. {
    intros x H4. rewrite Hr in H4. apply Specify.Charac in H4.
    destruct H4 as [H4 _]. apply SOC.IsOrdinal with (succ a). 2: assumption.
    apply Succ.IsOrdinal. assumption. }
  assert (a :< r) as H5. {
    rewrite Hr. apply Specify.Charac. split.
    - apply Succ.IsIn.
    - apply Cofinal.Refl. assumption. }
  assert (r <> :0:) as H6. { apply Empty.HasElem. exists a. assumption. }
  assert (forall c, c :< r -> b :<=: c) as H7. {
    intros c H7. rewrite Hr in H7. apply Specify.Charac in H7.
    destruct H7 as [H7 H8].
    assert (Ordinal c) as H9. { apply H4. rewrite Hr. apply Specify.Charac.
      split; assumption. }
    apply H3; assumption. }
  (* The infimum is the largest ordinal below every candidate.                  *)
  unfold charac. rewrite <- Hr. apply Inf.IsLargest; assumption.
Qed.

(* The character of cofinality of an ordinal is contained in the ordinal.       *)
Proposition IsIncl : forall (a:U), Ordinal a ->
  charac a :<=: a.
Proof.
(* Proof by Hermes + gpt 5.5                                                    *)
  intros a H1.
  (* Since a is cofinal with itself, the character is below a.                  *)
  apply IsLowerBound; try assumption. apply Cofinal.Refl. assumption.
Qed.

(* The character of cofinality of an ordinal is cofinal in that ordinal.        *)
Proposition IsCofinal : forall (a:U), Ordinal a ->
  Cofinal a (charac a).
Proof.
(* Proof by Hermes + gpt 5.5                                                    *)
  intros a H1.
  (* The candidates are the ordinals below succ a cofinal with a.               *)
  remember {{ x :< succ a | Cofinal a }} as r eqn:Hr.
  assert (toClass r :<=: Ordinal) as H2. {
    intros x H2. rewrite Hr in H2. apply Specify.Charac in H2.
    destruct H2 as [H2 _]. apply SOC.IsOrdinal with (succ a). 2: assumption.
    apply Succ.IsOrdinal. assumption. }
  assert (a :< r) as H3. {
    rewrite Hr. apply Specify.Charac. split.
    - apply Succ.IsIn.
    - apply Cofinal.Refl. assumption. }
  assert (r <> :0:) as H4. { apply Empty.HasElem. exists a. assumption. }
  assert (inf r :< r) as H5. { apply Inf.IsIn; assumption. }
  (* The infimum is itself a candidate, hence cofinal with a.                   *)
  unfold charac. rewrite Hr in H5.
  apply Specify.Charac in H5. destruct H5 as [_ H5]. assumption.
Qed.

(* The character of cofinality of an ordinal is a cardinal.                     *)
Proposition IsCardinal : forall (a:U), Ordinal a ->
  Cardinal (charac a).
Proof.
(* Proof by Hermes + gpt 5.5                                                    *)
  intros a H1.
  assert (Ordinal (charac a)) as H2. { apply IsOrdinal. }
  assert (forall b, Ordinal b -> charac a :~: b -> charac a :<=: b) as H3. {
    intros b H3 H4.
    assert (b :< charac a \/ charac a :<=: b) as H5. {
      apply SOC.ElemOrIncl; assumption. }
    destruct H5 as [H5|H5]. 2: assumption. exfalso.
    (* If a smaller ordinal were equipotent to charac a, it would contain an    *)
    (* even smaller cofinal ordinal, contradicting minimality of charac a.      *)
    assert (b :<=: charac a) as H6. { apply SOC.ElemIsIncl; assumption. }
    assert (exists c, c :<=: b /\ Cofinal (charac a) c) as H7. {
      apply Cofinal.ExtractEquiv; try assumption. apply SCE.Sym. assumption. }
    destruct H7 as [c [H7 H8]].
    assert (Ordinal c) as H9. {
      apply Cofinal.IsOrdinal with (charac a). assumption. }
    assert (Cofinal a c) as H10. {
      apply Cofinal.Tran with (charac a); try assumption. apply IsCofinal.
      assumption. }
    assert (charac a :<=: c) as H11. { apply IsLowerBound; assumption. }
    assert (c :< charac a) as H12. {
      apply SOC.InclElemTran with b; assumption. }
    assert (charac a :< charac a) as H13. {
      apply SOC.InclElemTran with c; assumption. }
    apply Foundation.NoLoop1 with (charac a). assumption. }
  apply SCC.Charac. split; assumption.
Qed.

(* The character of cofinality of zero is zero.                                 *)
Proposition WhenZero : charac :0: = :0:.
Proof.
(* Proof by Hermes + gpt 5.5                                                    *)
  apply Empty.WhenIncl. apply IsIncl. apply SOC.Zero.
Qed.

(* The character of cofinality of a successor ordinal is one.                   *)
Proposition WhenSucc : forall (a:U), Ordinal a ->
  charac (succ a) = :1:.
Proof.
(* Proof by Hermes + gpt 5.5                                                    *)
  intros a H1.
  assert (Ordinal (succ a)) as H2. { apply Succ.IsOrdinal. assumption. }
  assert (Cofinal (succ a) :1:) as H3. {
    apply Cofinal.WhenOne.
    - apply Natural.HasZeroRev. 1: assumption. apply Succ.HasZero. assumption.
    - apply Succ.IsSuccessor. assumption. }
  assert (charac (succ a) :<=: :1:) as H4. {
    apply IsLowerBound; try assumption. apply Natural.OneIsOrdinal. }
  assert (:1: :<=: charac (succ a)) as H5. {
    apply IsLargest; try assumption. 1: apply Natural.OneIsOrdinal.
    intros b H5 H6.
    assert (b <> :0:) as H7. {
      intros H7. subst. apply Cofinal.WhenZero in H6.
      apply Succ.NotZero with a. assumption. }
    assert (:0: :< b) as H8. { apply SOC.HasZero; assumption. }
    apply Natural.HasZeroRev; assumption. }
  apply Incl.Double. split; assumption.
Qed.

(* The character of cofinality of omega is omega.                               *)
Proposition WhenOmega : charac :N = :N.
Proof.
(* Proof by Hermes + gpt 5.5                                                    *)
  assert (charac :N :<=: :N) as H1. { apply IsIncl. apply Omega.IsOrdinal. }
  assert (:N :<=: charac :N) as H2. {
    apply IsLargest; try apply Omega.IsOrdinal.
    intros a H2 H3.
    (* Cofinality transports the limit property from omega to a.                *)
    assert (Limit :N <-> Limit a) as H4. {
      apply Cofinal.LimitCompat; try assumption. apply Omega.IsOrdinal. }
    assert (Limit a) as H5. { apply H4. apply Omega.IsLimit. }
    apply Omega.IsInclLimit. assumption. }
  apply Incl.Double. split; assumption.
Qed.
