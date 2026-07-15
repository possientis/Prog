Require Import ZF.Class.Cardinal.InfiniteCard.
Require Import ZF.Class.DiffBySet.
Require Import ZF.Class.Equiv.
Require Import ZF.Class.Order.E.
Require Import ZF.Class.Order.Isom.
Require Import ZF.Class.Order.Minimal.
Require Import ZF.Class.Ordinal.Monotone.
Require Import ZF.Class.Ordinal.Order.E.
Require Import ZF.Class.Relation.Domain.
Require Import ZF.Class.Relation.FunctionOn.
Require Import ZF.Set.Cardinal.Core.
Require Import ZF.Set.Core.
Require Import ZF.Set.Empty.
Require Import ZF.Set.Incl.
Require Import ZF.Set.Ordinal.Core.
Require Import ZF.Set.Ordinal.InfOfClass.
Require Import ZF.Set.Ordinal.Limit.
Require Import ZF.Set.Ordinal.Omega.
Require Import ZF.Set.Ordinal.Succ.
Require Import ZF.Set.Relation.EvalOfClass.
Require Import ZF.Set.Relation.ImageUnderClass.
Require Import ZF.Set.Relation.RestrictOfClass.
Require Import ZF.Set.UnionGenOfClass.

Module CCI := ZF.Class.Cardinal.InfiniteCard.
Module CMI := ZF.Class.Order.Minimal.
Module COC := ZF.Class.Ordinal.Core.
Module COE := ZF.Class.Ordinal.Order.E.
Module COM := ZF.Class.Ordinal.Monotone.
Module COS := ZF.Class.Ordinal.Subclass.
Module CFO := ZF.Class.Relation.FunctionOn.
Module SEM := ZF.Set.Empty.
Module SOC := ZF.Set.Ordinal.Core.
Module SUG := ZF.Set.UnionGenOfClass.

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
  - apply CCI.IsProper.
  - intros b. apply CCI.IsOrdinal.
Qed.

Proposition IsInf : forall (a:U), Ordinal a ->
  Aleph!a = inf (InfiniteCard :\: Aleph:[a]:).
Proof.
  intros a H1. apply COS.IsInf. 3: assumption.
  - apply CCI.IsProper.
  - intros b. apply CCI.IsOrdinal.
Qed.

(* Aleph is an isomorphism between the ordinals and infinite cardinals.         *)
Proposition IsIsom : Isom Aleph E E Ordinal InfiniteCard.
Proof.
  apply COS.IsIsom.
  - apply CCI.IsProper.
  - intros a. apply CCI.IsOrdinal.
Qed.

(* Aleph is the unique isomorphism ...                                          *)
Proposition IsUnique : forall (F:Class),
  Isom F E E Ordinal InfiniteCard -> F :~: Aleph.
Proof.
  intros F. apply COS.IsUnique.
  - apply CCI.IsProper.
  - intros a. apply CCI.IsOrdinal.
Qed.

(* Aleph is strictly monotone.                                                  *)
Proposition IsMonotone : Monotone Aleph.
Proof.
  apply COS.IsMonotone.
  - apply CCI.IsProper.
  - intros a. apply CCI.IsOrdinal.
Qed.

(* The domain of Aleph is the class of ordinals.                                *)
Proposition DomainOf : domain Aleph :~: Ordinal.
Proof.
  apply IsIsom.
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
  intros a H1. apply CCI.IsCardinal, IsInfiniteCard. assumption.
Qed.

(* Aleph(a) is no less than a.                                                  *)
Proposition IsIncl : forall (a:U), Ordinal a ->
  a :<=: Aleph!a.
Proof.
  intros a H1. apply COM.IsIncl.
  - apply IsMonotone.
  - apply DomainOf. assumption.
Qed.

(* At a limit ordinal, Aleph is the union of its earlier values.                *)
Proposition WhenLimit : forall (a:U), Limit a -> Aleph!a = :\/:_{a} Aleph.
Proof.
(* Proof by Hermes + gpt 5.5                                                    *)
  intros a H1.
  assert (Ordinal a) as H2. { apply H1. }
  assert (Aleph!a :<=: :\/:_{a} Aleph) as H20. {
    (* The minimality of Aleph(a) bounds it by the union of earlier values.     *)
    assert (Minimal E (InfiniteCard :\: Aleph:[a]:) Aleph!a) as H5. {
      apply IsMinimal. assumption. }
    assert (InfiniteCard (:\/:_{a} Aleph)) as H6. {
      apply CCI.UnionGen.
      - intros b H6. apply IsInfiniteCard.
        apply (SOC.IsOrdinal a); assumption.
      - apply SEM.HasElem. exists :0:.
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
        apply SUG.IsIncl. assumption. }
      assert (COM.Monotone Aleph) as H14. { apply IsMonotone. }
      destruct H14 as [_ H14].
      assert (Aleph!b :< Aleph!(succ b)) as H15. {
        apply H14; try apply DomainOf; try assumption. apply Succ.IsIn. }
      rewrite H9 in H15.
      assert (:\/:_{a} Aleph :< :\/:_{a} Aleph) as H16. {
        apply H13. assumption. }
      revert H16. apply Foundation.NoLoop1. }
    apply (COE.WhenMinimal (InfiniteCard :\: Aleph:[a]:)); try assumption.
    intros x H8. apply CCI.IsOrdinal. apply H8. }
  assert (:\/:_{a} Aleph :<=: Aleph!a) as H21. {
    (* Every earlier Aleph value is bounded by Aleph(a).                        *)
    apply SUG.WhenSetBounded. intros b H5.
    assert (Ordinal b) as H6. { apply (SOC.IsOrdinal a); assumption. }
    assert (COM.Monotone Aleph) as H8. { apply IsMonotone. }
    destruct H8 as [_ H8].
    assert (Aleph!b :< Aleph!a) as H9. {
      apply H8; try apply DomainOf; assumption. }
    apply SOC.ElemIsIncl. 2: assumption.
    apply CCI.IsOrdinal, IsInfiniteCard. assumption. }
  apply Incl.Double. split; assumption.
Qed.

