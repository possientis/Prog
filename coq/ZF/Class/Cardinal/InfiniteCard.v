Require Import ZF.Class.Cardinal.Core.
Require Import ZF.Class.DiffBySet.
Require Import ZF.Class.Empty.
Require Import ZF.Class.Equiv.
Require Import ZF.Class.Proper.
Require Import ZF.Set.Cardinal.Core.
Require Import ZF.Set.Core.
Require Import ZF.Set.Empty.
Require Import ZF.Set.Incl.
Require Import ZF.Set.Ordinal.Core.
Require Import ZF.Set.Ordinal.InfOfClass.
Require Import ZF.Set.Ordinal.Limit.
Require Import ZF.Set.Ordinal.Omega.
Require Import ZF.Set.Ordinal.Succ.
Require Import ZF.Set.Ordinal.Sup.
Require Import ZF.Set.Relation.EvalOfClass.
Require Import ZF.Set.UnionGenOfClass.

Module CCC := ZF.Class.Cardinal.Core.
Module CEM := ZF.Class.Empty.
Module SCC := ZF.Set.Cardinal.Core.
Module SOC := ZF.Set.Ordinal.Core.
Module SCE := ZF.Set.Cardinal.Equiv.
Module SEM := ZF.Set.Empty.
Module SOI := ZF.Set.Ordinal.InfOfClass.
Module SOS := ZF.Set.Ordinal.Sup.
Module SUG := ZF.Set.UnionGenOfClass.

(* The class of infinite cardinal numbers.                                      *)
Definition InfiniteCard : Class := Cardinal :\: :N.

(* The class of infinite cardinal numbers is a proper class.                    *)
Proposition IsProper : Proper InfiniteCard.
Proof.
  apply DiffBySet.IsProper, CCC.IsProper.
Qed.

Proposition IsCardinal : forall (a:U), InfiniteCard a ->
  Cardinal a.
Proof.
  apply DiffBySet.IsInclL.
Qed.

Proposition IsOrdinal : forall (a:U), InfiniteCard a ->
  Ordinal a.
Proof.
  intros a H1. apply SCC.CardIsOrd, IsCardinal. assumption.
Qed.

(* omega is a cardinal number not contained in itself.                          *)
Proposition HasOmega : InfiniteCard :N.
Proof.
  (* Proof by Claude + sonnet 4.6                                               *)
  (* N is a cardinal number not a member of itself by foundation.               *)
  split.
  - apply SCC.HasOmega.
  - apply Foundation.NoLoop1.
Qed.

(* Every infinite cardinal contains omega as a subset.                          *)
Proposition IsIncl : forall (a:U),  InfiniteCard a ->
  :N :<=: a.
Proof.
  (* Proof by Claude + sonnet 4.6                                               *)
  (* An infinite cardinal a is an ordinal not in omega. Since ordinals are      *)
  (* totally ordered by membership, either a is in omega or omega is included   *)
  (* in a. The first is ruled out, so omega is a subset of a.                   *)
  intros a H1.
  assert (a :< :N \/ :N :<=: a) as H2. {
    apply SOC.ElemOrIncl.
    - apply IsOrdinal. assumption.
    - apply Omega.IsOrdinal. }
  destruct H2 as [H2|H2]. 2: assumption. exfalso.
  apply DiffBySet.Charac in H1. destruct H1 as [_ H3].
  apply H3. assumption.
Qed.

(* The infimum of the class of infinite cardinals is omega.                     *)
Proposition Inf : inf InfiniteCard = :N.
Proof.
  (* Proof by Claude + sonnet 4.6                                               *)
  (* We prove double inclusion. Omega is an infinite cardinal, so the infimum   *)
  (* is at most omega. Every infinite cardinal contains omega, so omega is a    *)
  (* lower bound, and the infimum is at least omega.                            *)
  apply Incl.Double. split.
  - (* The infimum is at most omega, since omega is an infinite cardinal.       *)
    apply SOI.IsLowerBound.
    + intros a H1. apply IsOrdinal. assumption.
    + apply HasOmega.
  - (* The infimum is at least omega: omega is a lower bound of the class.      *)
    apply SOI.IsLargest.
    + intros a H1. apply IsOrdinal. assumption.
    + (* The class of infinite cardinals is non-empty, as it contains omega.    *)
      apply CEM.HasElem. exists :N. apply HasOmega.
    + (* Every infinite cardinal contains omega.                                *)
      intros a H1. apply IsIncl. assumption.
Qed.

(* The supremum of a non-empty set of infinite cardinals is infinite.           *)
Proposition Sup : forall (a:U),
  toClass a :<=: InfiniteCard   ->
  a <> :0:                      ->
  InfiniteCard (sup a).
Proof.
(* Proof by Hermes + gpt 5.5                                                    *)
  intros a H1 H2.
  split.
  - (* The supremum is a cardinal because all members are cardinals.            *)
    apply SCC.Sup. intros b H3. apply IsCardinal, H1. assumption.
  - (* A member of the set contains omega, and is contained in the supremum.    *)
    assert (exists b, b :< a) as H3. {
      apply SEM.HasElem. assumption. }
    destruct H3 as [b H3].
    assert (InfiniteCard b) as H4. { apply H1. assumption. }
    assert (:N :<=: b) as H5. { apply IsIncl. assumption. }
    assert (toClass a :<=: Ordinal) as H6. {
      intros c H6. apply IsOrdinal, H1. assumption. }
    assert (b :<=: sup a) as H7. { apply SOS.IsUpperBound; assumption. }
    assert (:N :<=: sup a) as H8. { apply Incl.Tran with b; assumption. }
    intros H9.
    assert (sup a :< sup a) as H10. { apply H8. assumption. }
    revert H10. apply Foundation.NoLoop1.
Qed.

(* A non-empty union of set-indexed infinite cardinals is infinite.             *)
Proposition UnionGen : forall (A:Class) (a:U),
  (forall x, x :< a -> InfiniteCard (A!x))  ->
  a <> :0:                                  ->
  InfiniteCard (:\/:_{a} A).
Proof.
(* Proof by Hermes + gpt 5.5                                                    *)
  intros A a H1 H2. split.
  - (* The union is a cardinal because every value is a cardinal.               *)
    apply SCC.UnionGen. intros x H3. apply IsCardinal, H1. assumption.
  - (* One value contains omega, and that value is included in the union.       *)
    assert (exists b, b :< a) as H3. { apply SEM.HasElem. assumption. }
    destruct H3 as [b H3].
    assert (InfiniteCard (A!b)) as H4. { apply H1. assumption. }
    assert (:N :<=: A!b) as H5. { apply IsIncl. assumption. }
    assert (A!b :<=: :\/:_{a} A) as H6. { apply SUG.IsIncl. assumption. }
    assert (:N :<=: :\/:_{a} A) as H7. {
      apply Incl.Tran with (A!b); assumption. }
    intros H8.
    assert (:\/:_{a} A :< :\/:_{a} A) as H9. { apply H7. assumption. }
    revert H9. apply Foundation.NoLoop1.
Qed.

(* Every infinite cardinal is a limit ordinal.                                  *)
Proposition IsLimit : forall (a:U), InfiniteCard a ->
  Limit a.
Proof.
  (* Proof by Claude + sonnet 4.6                                               *)
  (* An infinite cardinal is not zero and not a successor ordinal.              *)
  intros a H1.
  assert (Ordinal a) as H2. { apply IsOrdinal. assumption. }
  apply Limit.ThreeWay in H2. destruct H2 as [H3|[H3|H3]]. 3: assumption.
  - (* :0: belongs to omega so :0: is not an infinite cardinal.                 *)
    exfalso. subst.
    apply DiffBySet.Charac in H1. destruct H1 as [_ H1].
    apply H1. apply Omega.HasZero.
  - (* a is a successor, say a = succ b where b is an ordinal.                  *)
    exfalso. destruct H3 as [b [H4 H3]]. subst.
    (* Since succ b is infinite, b is not in omega (else succ b would be).      *)
    assert (:N :<=: b) as H5. {
      assert (b :< :N \/ :N :<=: b) as H5. {
        apply SOC.ElemOrIncl; try assumption. apply Omega.IsOrdinal. }
      destruct H5 as [H5|H5]. 2: assumption. exfalso.
      apply DiffBySet.Charac in H1. destruct H1 as [_ H1]. apply H1.
      apply Omega.HasSucc. assumption. }
    (* So omega is a subset of b, and the Hilbert hotel gives b ~ succ b = a.   *)
    assert (b :~: succ b) as H6. { apply SCE.Succ; assumption. }
    (* But b is strictly below a = card a, contradicting that a is a cardinal.  *)
    assert (succ b = card (succ b)) as H7. {
      apply SCC.WhenCardinal, IsCardinal. assumption. }
    apply (SCC.IsNotEquiv (succ b) b); try assumption.
    + rewrite <- H7. apply Succ.IsIn.
    + apply SCE.Sym. assumption.
Qed.
