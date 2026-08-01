Require Import ZF.Class.Cardinal.InfiniteCard.
Require Import ZF.Class.DiffBySet.
Require Import ZF.Class.Equiv.
Require Import ZF.Class.Order.E.
Require Import ZF.Class.Order.Isom.
Require Import ZF.Class.Order.Minimal.
Require Import ZF.Class.Ordinal.Monotone.
Require Import ZF.Class.Ordinal.Order.E.
Require Import ZF.Class.Relation.Bij.
Require Import ZF.Class.Relation.Domain.
Require Import ZF.Class.Relation.FunctionOn.
Require Import ZF.Set.Cardinal.Number.
Require Import ZF.Set.Core.
Require Import ZF.Set.Empty.
Require Import ZF.Set.Incl.
Require Import ZF.Set.Ordinal.Ordinal.
Require Import ZF.Set.Ordinal.InfOfClass.
Require Import ZF.Set.Ordinal.Limit.
Require Import ZF.Set.Ordinal.Monotone.
Require Import ZF.Set.Ordinal.Omega.
Require Import ZF.Set.Ordinal.Succ.
Require Import ZF.Set.Relation.EvalOfClass.
Require Import ZF.Set.Relation.Fun.
Require Import ZF.Set.Relation.ImageUnderClass.
Require Import ZF.Set.Relation.RestrictOfClass.
Require Import ZF.Set.UnionGenOfClass.

Module CMI := ZF.Class.Order.Minimal.
Module CEE := ZF.Class.Order.E.
Module COE := ZF.Class.Ordinal.Order.E.
Module COM := ZF.Class.Ordinal.Monotone.
Module COS := ZF.Class.Ordinal.Subclass.
Module CBJ := ZF.Class.Relation.Bij.
Module CFO := ZF.Class.Relation.FunctionOn.

(* MinFresh picks the E-minimal element of InfiniteCard not already in range.   *)
Definition MinFresh : Class := COS.MinFresh InfiniteCard.

(* The unique isomorphism between the ordinals and the infinite cardinals.      *)
Definition Aleph : Class := COS.Enum InfiniteCard.

(* Aleph is a function class defined on the ordinals.                           *)
Proposition IsFunctionOn : FunctionOn Aleph Ordinal.
Proof.
  apply COS.IsFunctionOn.
Qed.

(* Aleph is MinFresh-recursive.                                                 *)
Proposition IsRecursive : forall (a:U), Ordinal a ->
  Aleph!a = MinFresh!(Aleph :|: a).
Proof.
  apply COS.IsRecursive.
Qed.

(* Aleph(a) is the least infinite cardinal not in the image aleph[a].           *)
Proposition IsMinimal : forall (a:U), Ordinal a ->
  Minimal E (InfiniteCard :\: Aleph:[a]:) Aleph!a.
Proof.
  intros a H1.
  apply COS.IsMinimal. 3: assumption.
  - apply InfiniteCard.IsProper.
  - intros b. apply InfiniteCard.IsOrdinal.
Qed.

Proposition IsInf : forall (a:U), Ordinal a ->
  Aleph!a = inf (InfiniteCard :\: Aleph:[a]:).
Proof.
  intros a H1. apply COS.IsInf. 3: assumption.
  - apply InfiniteCard.IsProper.
  - intros b. apply InfiniteCard.IsOrdinal.
Qed.

(* Aleph is an isomorphism between the ordinals and infinite cardinals.         *)
Proposition IsIsom : Isom Aleph E E Ordinal InfiniteCard.
Proof.
  apply COS.IsIsom.
  - apply InfiniteCard.IsProper.
  - intros a. apply InfiniteCard.IsOrdinal.
Qed.

(* Every infinite cardinal appears as an Aleph value.                           *)
Proposition HasIndex : forall (a:U),
  InfiniteCard a -> exists b, Ordinal b /\ Aleph!b = a.
Proof.
(* Proof by Hermes + gpt 5.5                                                    *)
  intros a H1.
  assert (Bij Aleph Ordinal InfiniteCard) as H2. { apply IsIsom. }
  assert (InfiniteCard a <-> exists b, Ordinal b /\ Aleph!b = a) as H3. {
    apply CBJ.RangeCharac. assumption. }
  apply H3. assumption.
Qed.

(* Aleph is the unique isomorphism ...                                          *)
Proposition IsUnique : forall (F:Class),
  Isom F E E Ordinal InfiniteCard -> F :~: Aleph.
Proof.
  intros F. apply COS.IsUnique.
  - apply InfiniteCard.IsProper.
  - intros a. apply InfiniteCard.IsOrdinal.
Qed.

(* Aleph is strictly monotone.                                                  *)
Proposition IsMonotone : COM.Monotone Aleph.
Proof.
  apply COS.IsMonotone.
  - apply InfiniteCard.IsProper.
  - intros a. apply InfiniteCard.IsOrdinal.
Qed.

(* The domain of Aleph is the class of ordinals.                                *)
Proposition DomainOf : domain Aleph :~: Ordinal.
Proof.
  apply IsIsom.
Qed.

(* Aleph preserves strict comparison between ordinal indices.                   *)
Proposition ElemCompat : forall (a b:U), Ordinal a -> Ordinal b ->
  a :< b -> Aleph!a :< Aleph!b.
Proof.
(* Proof by Hermes + gpt 5.5                                                    *)
  intros a b H1 H2 H3.
  assert (COM.Monotone Aleph) as H4. { apply IsMonotone. }
  destruct H4 as [_ H4].
  assert (domain Aleph a) as H5. { apply DomainOf. assumption. }
  assert (domain Aleph b) as H6. { apply DomainOf. assumption. }
  apply H4; assumption.
Qed.

(* Aleph reflects strict comparison between ordinal indices.                    *)
Proposition ElemCompatRev : forall (a b:U), Ordinal a -> Ordinal b ->
  Aleph!a :< Aleph!b -> a :< b.
Proof.
(* Proof by Hermes + gpt 5.5                                                    *)
  intros a b H1 H2 H3.
  assert (Isom Aleph E E Ordinal InfiniteCard) as H4. { apply IsIsom. }
  destruct H4 as [_ H4].
  apply CEE.Charac2.
  apply H4; try assumption. apply CEE.Charac2. assumption.
Qed.

(* The Aleph value at an ordinal is an infinite cardinal.                       *)
Proposition IsInfiniteCard : forall (a:U), Ordinal a ->
  InfiniteCard Aleph!a.
Proof.
(* Proof by Hermes + gpt 5.5                                                    *)
  intros a H1.
  assert (Minimal E (InfiniteCard :\: Aleph:[a]:) Aleph!a) as H2. {
    apply IsMinimal. assumption. }
  assert ((InfiniteCard :\: Aleph:[a]:) Aleph!a) as H3. {
    apply CMI.IsIn with E. assumption. }
  apply H3.
Qed.

(* The Aleph value at an ordinal is a cardinal.                                 *)
Proposition IsCardinal : forall (a:U), Ordinal a ->
  Cardinal Aleph!a.
Proof.
(* Proof by Hermes + gpt 5.5                                                    *)
  intros a H1. apply InfiniteCard.IsCardinal, IsInfiniteCard. assumption.
Qed.

(* The Aleph value at an ordinal is an ordinal.                                 *)
Proposition IsOrdinal : forall (a:U), Ordinal a ->
  Ordinal Aleph!a.
Proof.
(* Proof by Hermes + gpt 5.5                                                    *)
  intros a H1. apply Number.CardIsOrd, IsCardinal. assumption.
Qed.

(* Aleph preserves inclusion between ordinal indices.                           *)
Proposition InclCompat : forall (a b:U), Ordinal a -> Ordinal b ->
  a :<=: b -> Aleph!a :<=: Aleph!b.
Proof.
(* Proof by Hermes + gpt 5.5                                                    *)
  intros a b H1 H2 H3.
  apply Ordinal.EqualOrElem in H3; try assumption.
  destruct H3 as [H3|H3].
  - subst. apply Incl.Refl.
  - apply Ordinal.ElemIsIncl.
    + apply IsOrdinal. assumption.
    + apply ElemCompat; assumption.
Qed.

(* Aleph(a) is no less than a.                                                  *)
Proposition IsIncl : forall (a:U), Ordinal a ->
  a :<=: Aleph!a.
Proof.
  intros a H1. apply COM.IsIncl.
  - apply IsMonotone.
  - apply DomainOf. assumption.
Qed.

(* The zeroth infinite cardinal is omega.                                       *)
Proposition WhenZero : Aleph!:0: = :N.
Proof.
(* Proof by Hermes + gpt 5.5                                                    *)
  (* Aleph(0) is the infimum of the infinite cardinals not already attained.    *)
  assert (Aleph!:0: = inf (InfiniteCard :\: Aleph:[:0:]:)) as H1. {
    apply IsInf. apply Ordinal.Zero. }
  assert (Aleph:[:0:]: = :0:) as H2. {
    apply ImageUnderClass.WhenZero. reflexivity. }
  rewrite H1, H2. transitivity (inf InfiniteCard).
  - apply InfOfClass.EquivCompat. apply DiffBySet.IdentityR.
  - apply InfiniteCard.Inf.
Qed.

(* Sets below a successor Aleph have cardinal at most the previous Aleph.       *)
Proposition CardBelowSucc : forall (a x:U), Ordinal a ->
  x :< Aleph! (succ a) -> card x :<=: Aleph!a.
Proof.
(* Proof by Hermes + gpt 5.5                                                    *)
  intros a x H1 H2.
  assert (Ordinal :N) as G0. { apply Omega.IsOrdinal. }
  assert (Ordinal (succ a)) as G1. { apply Succ.IsOrdinal. assumption. }
  assert (Ordinal Aleph! (succ a)) as G2. { apply IsOrdinal. assumption. }
  assert (Ordinal x) as G3. {
    apply Ordinal.IsOrdinal with Aleph!(succ a); assumption. }
  assert (Cardinal Aleph!a) as G4. { apply IsCardinal. assumption. }
  assert (Cardinal Aleph!(succ a)) as G5. { apply IsCardinal. assumption. }
  assert (Ordinal (card x)) as G6. { apply Number.IsOrdinal. }
  assert (card x :< Aleph!(succ a)) as H3. { apply Number.CardLess; assumption. }
  assert (card x :< :N \/ :N :<=: card x) as H4. {
    apply Ordinal.ElemOrIncl; assumption. }
  destruct H4 as [H4|H4].
  - (* Finite cardinals are bounded by Aleph(0), hence by Aleph(a).             *)
    assert (card x :<=: :N) as H5. { apply Ordinal.ElemIsIncl; assumption. }
    assert (:N :<=: Aleph!a) as H6. {
      rewrite <- WhenZero. apply InclCompat; try assumption.
      - apply Ordinal.Zero.
      - apply Empty.IsIncl. }
    apply Incl.Tran with :N; assumption.
  - (* An infinite cardinal below Aleph(a+1) is an earlier Aleph value.         *)
    assert (Cardinal (card x)) as H5. { exists x. reflexivity. }
    assert (InfiniteCard (card x)) as H6. {
      apply InfiniteCard.WhenIncl; assumption. }
    assert (exists b, Ordinal b /\ Aleph!b = card x) as H7. {
      apply HasIndex. assumption. }
    destruct H7 as [b [H7 H8]].
    assert (Aleph!b :< Aleph!(succ a)) as H9. { rewrite H8. assumption. }
    assert (b :< succ a) as H10. { apply ElemCompatRev; try assumption. }
    apply Succ.Charac in H10. destruct H10 as [H10|H10].
    + subst. rewrite <- H8. apply Incl.Refl.
    + assert (b :<=: a) as H11. { apply Ordinal.ElemIsIncl; assumption. }
      assert (Aleph!b :<=: Aleph!a) as H12. { apply InclCompat; assumption. }
      rewrite <- H8. assumption.
Qed.

(* At a limit ordinal, Aleph is the union of its earlier values.                *)
Proposition Continuous : forall (a:U), Limit a -> Aleph!a = :\/:_{a} Aleph.
Proof.
(* Proof by Hermes + gpt 5.5                                                    *)
  intros a H1.
  assert (Ordinal a) as H2. { apply H1. }
  assert (Aleph!a :<=: :\/:_{a} Aleph) as H20. {
    (* The minimality of Aleph(a) bounds it by the union of earlier values.     *)
    assert (Minimal E (InfiniteCard :\: Aleph:[a]:) Aleph!a) as H5. {
      apply IsMinimal. assumption. }
    assert (InfiniteCard (:\/:_{a} Aleph)) as H6. {
      apply InfiniteCard.UnionGen.
      - intros b H6. apply IsInfiniteCard.
        apply (Ordinal.IsOrdinal a); assumption.
      - apply Empty.HasElem. exists :0:.
        apply Limit.HasZero. assumption. }
    assert ((InfiniteCard :\: Aleph:[a]:) (:\/:_{a} Aleph)) as H7. {
      split. 1: assumption.
      intros H7.
      apply (CFO.ImageSetCharac Aleph Ordinal a) in H7.
      2: apply IsFunctionOn.
      destruct H7 as [b [H7 [H8 H9]]].
      assert (succ b :< a) as H10. { apply Limit.HasSucc; assumption. }
      assert (Ordinal (succ b)) as H11. { apply Succ.IsOrdinal. assumption. }
      assert (Aleph!(succ b) :<=: :\/:_{a} Aleph) as H13. {
        apply UnionGenOfClass.IsIncl. assumption. }
      assert (COM.Monotone Aleph) as H14. { apply IsMonotone. }
      destruct H14 as [_ H14].
      assert (Aleph!b :< Aleph!(succ b)) as H15. {
        apply H14; try apply DomainOf; try assumption. apply Succ.IsIn. }
      rewrite H9 in H15.
      assert (:\/:_{a} Aleph :< :\/:_{a} Aleph) as H16. {
        apply H13. assumption. }
      revert H16. apply Foundation.NoLoop1. }
    apply (COE.WhenMinimal (InfiniteCard :\: Aleph:[a]:)); try assumption.
    intros x H8. apply InfiniteCard.IsOrdinal. apply H8. }
  assert (:\/:_{a} Aleph :<=: Aleph!a) as H21. {
    (* Every earlier Aleph value is bounded by Aleph(a).                        *)
    apply UnionGenOfClass.WhenSetBounded. intros b H5.
    assert (Ordinal b) as H6. { apply (Ordinal.IsOrdinal a); assumption. }
    assert (COM.Monotone Aleph) as H8. { apply IsMonotone. }
    destruct H8 as [_ H8].
    assert (Aleph!b :< Aleph!a) as H9. {
      apply H8; try apply DomainOf; assumption. }
    apply Ordinal.ElemIsIncl. 2: assumption.
    apply IsOrdinal. assumption. }
  apply Incl.Double. split; assumption.
Qed.

