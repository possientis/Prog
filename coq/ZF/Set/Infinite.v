Require Import ZF.Axiom.Choice.
Require Import ZF.Axiom.Classic.
Require Import ZF.Class.Cardinal.InfiniteCard.
Require Import ZF.Class.Empty.
Require Import ZF.Class.Equiv.
Require Import ZF.Set.Core.
Require Import ZF.Set.Diff.
Require Import ZF.Set.Empty.
Require Import ZF.Set.Finite.
Require Import ZF.Set.Incl.
Require Import ZF.Set.Less.
Require Import ZF.Set.Cardinal.Core.
Require Import ZF.Set.Cardinal.Equiv.
Require Import ZF.Set.Cardinal.WellOrderable.
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
Module CCI := ZF.Class.Cardinal.InfiniteCard.
Module SCC := ZF.Set.Cardinal.Core.
Module SCE := ZF.Set.Cardinal.Equiv.
Module SCW := ZF.Set.Cardinal.WellOrderable.
Module SOC := ZF.Set.Ordinal.Core.
Module SOI := ZF.Set.Ordinal.InfOfClass.

(* A set is infinite if and only if it is not finite.                           *)
Definition Infinite (a:U) : Prop := ~ Finite a.

(* Being infinite is preserved under equipotence.                               *)
Proposition EquivCompat : forall (a b:U),
  a :~: b -> Infinite a -> Infinite b.
Proof.
  (* Proof by Claude + sonnet 4.6                                               *)
  (* Infinite a means not Finite a. If b were finite, a ~ b would give          *)
  (* Finite a via Finite.EquivCompat, contradicting Infinite a.                 *)
  intros a b H1 H2 H3. apply H2.
  apply Finite.EquivCompat with b. 2: assumption.
  apply SCE.Sym. assumption.
Qed.

(* The cardinal of an infinite set is not finite.                               *)
Proposition CardGen : forall (a:U), Infinite a ->
  WellOrderable a -> :N :<=: card a.
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


(* Assuming choice, an infinite set has cardinal at least omega.                *)
Proposition Card : forall (a:U), Choice ->
  Infinite a <-> :N :<=: card a.
Proof.
  intros a AC.
  assert (exists b, Ordinal b /\ a :~: b) as H1. {
    apply SCW.IsWellOrderable. assumption. }
  split; intros H2.
  - apply CardGen; assumption.
  - intros [n [H3 H4]].
    assert (card a = card n) as H5. { apply SCC.WhenEquiv. assumption. }
    assert (card n = n) as H6. { apply SCC.WhenNat. assumption. }
    assert (n :< n) as H7. { rewrite H5, H6 in H2. apply H2. assumption. }
    revert H7. apply Foundation.NoLoop1.
Qed.

(* Assuming choice, a set is infinite iff its cardinal is infinite.             *)
Proposition Charac : forall (a:U), Choice ->
  Infinite a <-> InfiniteCard (card a).
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros a AC. split; intros H1.
  - (* The cardinal is a cardinal number, and omega embeds into it.             *)
    split.
    + exists a. reflexivity.
    + assert (:N :<=: card a) as H2. { apply Card; assumption. }
      intros H3.
      assert (card a :< card a) as H4. { apply H2. assumption. }
      revert H4. apply Foundation.NoLoop1.
  - (* An infinite cardinal contains omega, so the set cannot be finite.        *)
    apply Card. 1: assumption. apply CCI.IsIncl. assumption.
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
    assert (WellOrderable a \/ ~ WellOrderable a) as [H4|H4]. {
      apply LawExcludedMiddle. }
    - assert (:N :<=: card a) as H5. { apply CardGen; assumption. }
      assert (card a :~: succ (card a)) as H6. { apply Equiv.Succ; assumption. }
      assert (succ a :~: card a) as H7. {
        apply SCE.Tran with (succ (card a)).
        - apply SCE.SuccCompat, IsEquivGen. assumption.
        - apply SCE.Sym. assumption. }
      apply SCC.IsLowerBound; assumption.
    - assert (~ WellOrderable (succ a)) as H5. {
        intros H5. apply H4. apply SCW.WellOrderableSuccRev. assumption. }
      assert (card (succ a) = :0:) as H6. {
        apply SCC.WhenNotWellOrderable. assumption. }
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

(* Assuming choice, an infinite set has a strict subset equipotent to it.       *)
Proposition Dedekind : forall (a:U), Choice -> Infinite a ->
  exists b, b :<: a /\ b :~: a.
Proof.
  (* Proof by Claude + sonnet 4.6                                               *)
  intros a AC H1.
  (* The empty set is finite, so a is nonempty.                                 *)
  assert (a <> :0:) as H2. {
    intros H2. apply H1. rewrite H2. apply Finite.Zero. }
  apply Empty.HasElem in H2. destruct H2 as [x H2].
  (* Pick x in a and let b = a \ {x}.                                           *)
  exists (a :\: :{x}:). split.
  - (* x is in a but not in b, so b is a strict subset of a.                    *)
    apply Less.Exists. split.
    + apply Diff.IsIncl.
    + exists x. split. 1: assumption.
      intros H3. apply Diff.Charac in H3. destruct H3 as [_ H3].
      apply H3. apply Single.IsIn.
  - apply SCC.EquivCharac. 1: assumption.
    assert ((a :\: :{x}:) :\/: :{x}: = a) as H3. {
      apply Diff.RemoveAddElem. assumption. }
    (* b is infinite: if finite, a = b u {x} would also be finite.              *)
    assert (Infinite (a :\: :{x}:)) as H4. {
      intros H4. apply H1. rewrite <- H3. apply Finite.AddElem. assumption. }
    (* Since a = b u {x} and b is infinite, card b = card a.                    *)
    assert (card (a :\: :{x}:) = card ((a :\: :{x}:) :\/: :{x}:)) as H5. {
      apply AddElem. assumption. }
    rewrite H3 in H5. assumption.
Qed.

(* Assuming choice, every infinite set has a countably infinite subset.         *)
Proposition HasOmegaSubset : forall (a:U), Choice -> Infinite a ->
  exists b, b :<=: a /\ b :~: :N.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros a AC H1.
  (* The cardinal of an infinite set contains N, so a has a subset of size N.   *)
  assert (:N :<=: card a) as H2. { apply Card; assumption. }
  apply SCC.HasSubsetOfSize; assumption.
Qed.

