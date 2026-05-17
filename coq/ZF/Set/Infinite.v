Require Import ZF.Axiom.Choice.
Require Import ZF.Axiom.Classic.
Require Import ZF.Class.Empty.
Require Import ZF.Class.Equiv.
Require Import ZF.Set.Core.
Require Import ZF.Set.Empty.
Require Import ZF.Set.Finite.
Require Import ZF.Set.Incl.
Require Import ZF.Set.Cardinal.Core.
Require Import ZF.Set.Cardinal.Equiv.
Require Import ZF.Set.Foundation.
Require Import ZF.Set.Ordinal.Core.
Require Import ZF.Set.Ordinal.InfOfClass.
Require Import ZF.Set.Ordinal.Omega.
Require Import ZF.Set.Ordinal.Succ.
Require Import ZF.Set.Relation.Bij.
Require Import ZF.Set.Relation.Image.
Require Import ZF.Set.Relation.Restrict.
Require Import ZF.Set.Single.
Require Import ZF.Set.Union2.

Module CEM := ZF.Class.Empty.
Module SCC := ZF.Set.Cardinal.Core.
Module SCE := ZF.Set.Cardinal.Equiv.
Module SOC := ZF.Set.Ordinal.Core.
Module SOI := ZF.Set.Ordinal.InfOfClass.

(* A set is infinite if and only if it is not finite.                           *)
Definition Infinite (a:U) : Prop := ~ Finite a.

(* Infiniteness is preserved under equipotence.                                 *)
Proposition EquivCompat : forall (a b:U),
  a :~: b -> Infinite a -> Infinite b.
Proof.
  (* Proof by Claude.                                                           *)
  (* Infinite a means not Finite a. If b were finite, a ~ b would give          *)
  (* Finite a via Finite.EquivCompat, contradicting Infinite a.                 *)
  intros a b H1 H2 H3. apply H2.
  apply Finite.EquivCompat with b. 2: assumption.
  apply SCE.Sym. assumption.
Qed.

(* The cardinal of an infinite set is not finite.                               *)
Proposition CardNotFiniteGen : forall (a:U), Infinite a ->
  WithOrdinal a -> :N :<=: card a.
Proof.
  intros a H1 H2.
  assert (Ordinal (card a)) as G1. { apply SCC.IsOrdinal. }
  assert (Ordinal :N) as G2. { apply Omega.IsOrdinal. }
  assert (card a :< :N \/ :N :<=: card a) as H3. {
    apply SOC.ElemOrIncl; assumption. }
  destruct H3 as [H3|H3]. 2: assumption. exfalso.
  apply H1. exists (card a). split. 1: assumption.
  apply SCC.IsEquivGen. assumption.
Qed.


(* The cardinal of an infinite set is not finite.                               *)
Proposition CardNotFinite : forall (a:U), Choice ->
  Infinite a <-> :N :<=: card a.
Proof.
  intros a AC.
  assert (exists b, Ordinal b /\ a :~: b) as H1. {
    apply SCE.HasOrdinal. assumption. }
  split; intros H2.
  - apply CardNotFiniteGen; assumption.
  - intros [n [H3 H4]].
    assert (card a = card n) as H5. { apply SCC.WhenEquiv. assumption. }
    assert (card n = n) as H6. { apply SCC.WhenNat. assumption. }
    assert (n :< n) as H7. { rewrite H5, H6 in H2. apply H2. assumption. }
    revert H7. apply Foundation.NoLoop1.
Qed.

(* For an infinite set, the cardinal of the successor is the cardinal.          *)
Proposition CardOfSucc : forall (a:U), Infinite a ->
  card (succ a) = card a.
Proof.
  intros a H1.
  assert (Ordinal (card a)) as G1. { apply SCC.IsOrdinal. }
  assert (card a :<=: card (succ a)) as H2. { apply SCC.IsInclSucc. }
  assert (card (succ a) :<=: succ (card a)) as H3. { apply SCC.IsInclSucc'. }
  assert (card (succ a) :<=: card a) as H4. {
    assert (WithOrdinal a \/ ~ WithOrdinal a) as [H4|H4]. {
      apply LawExcludedMiddle. }
    - assert (:N :<=: card a) as H5. { apply CardNotFiniteGen; assumption. }
      assert (card a :~: succ (card a)) as H6. { apply Equiv.Succ; assumption. }
      assert (succ a :~: card a) as H7. {
        apply SCE.Tran with (succ (card a)).
        - apply SCE.SuccCompat, IsEquivGen. assumption.
        - apply SCE.Sym. assumption. }
      apply SCC.IsLowerBound; assumption.
    - assert (~ WithOrdinal (succ a)) as H5. {
        intros H5. apply H4. apply SCE.WithOrdinalSuccRev. assumption. }
      assert (card (succ a) = :0:) as H6. {
        apply SCC.WhenNoOrdinal. assumption. }
      rewrite H6. apply Empty.IsIncl. }
  apply Incl.Double. split; assumption.
Qed.

(* Adding an element to an infinite set does not change its cardinal.           *)
Proposition AddElem : forall (a b:U), Infinite a ->
  card a = card (a :\/: :{b}:).
Proof.
  intros a b H1.
  assert (a :\/: :{b}: = a \/ a :\/: :{b}: :~: succ a) as [H2|H2]. {
    apply SCE.AddElem. }
  - rewrite H2. reflexivity.
  - assert (card (a :\/: :{b}:) = card (succ a)) as H3. {
      apply SCC.WhenEquiv. assumption. }
    rewrite H3. symmetry. apply CardOfSucc. assumption.
Qed.
