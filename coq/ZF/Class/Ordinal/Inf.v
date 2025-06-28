Require Import ZF.Class.Core.
Require Import ZF.Class.Diff.
Require Import ZF.Class.Empty.
Require Import ZF.Class.Incl.
Require Import ZF.Class.Inter.
Require Import ZF.Class.Inter2.
Require Import ZF.Class.IsSetOf.
Require Import ZF.Class.Less.
Require Import ZF.Class.Order.E.
Require Import ZF.Class.Order.InitSegment.
Require Import ZF.Class.Order.Minimal.
Require Import ZF.Class.Ordinal.Core.
Require Import ZF.Class.Ordinal.Inter.
Require Import ZF.Class.Small.
Require Import ZF.Class.Relation.InvImage.
Require Import ZF.Set.Core.
Require Import ZF.Set.Foundation.
Require Import ZF.Set.OrdPair.
Require Import ZF.Set.Single.

(* The infimum of the class A.                                                  *)
Definition inf (A:Class) : Class := :I(A :/\: On).

(* The infimum operation is compatible with class equivalence.                  *)
Proposition EquivCompat : forall (A B:Class),
  A :~: B -> inf A :~: inf B.
Proof.
  intros A B H1. apply Inter.EquivCompat, Inter2.EquivCompatL. assumption.
Qed.

Proposition InterOn : forall (A:Class), inf A :~: inf (A :/\: On).
Proof.
  intros A.
  apply Inter.EquivCompat, EquivSym, Inter2.WhenInclL, Inter2.IsInclR.
Qed.

(* The infimum of a class of ordinals coincide with its intersection.           *)
Proposition WhenOrdinalElem : forall (A:Class),
  A :<=: On -> :I(A) :~: inf A.
Proof.
  intros A H1. unfold inf. apply Inter.EquivCompat.
  apply EquivSym, Class.Inter2.WhenInclL. assumption.
Qed.

(* The infimum of a class is an ordinal class.                                 *)
Proposition IsOrdinal : forall (A:Class), Ordinal (inf A).
Proof.
  intros A. apply Ordinal.Inter.IsOrdinal, Class.Inter2.IsInclR.
Qed.

(* The infimum of a class is small.                                             *)
Proposition IsSmall : forall (A:Class), Small (inf A).
Proof.
  intros A. apply Inter.IsSmall.
Qed.

(* The infimum of a class is a strict subclass of On.                           *)
Proposition IsLess : forall (A:Class), inf A :<: On.
Proof.
  intros A.
  assert (inf A :~: On \/ inf A :<: On) as H1. {
    apply Core.IsOnOrLess, IsOrdinal. }
  destruct H1 as [H1|H1]. 2: assumption. exfalso.
  apply OnIsProper. apply Small.EquivCompat with (inf A).
  1: assumption. apply IsSmall.
Qed.

(* The infimum of a class of ordinals is a lower-bound.                         *)
Proposition IsLowerBound : forall (A:Class) (a:U),
  A :<=: On -> A a -> inf A :<=: toClass a.
Proof.
  intros A a H1 H2. apply Incl.EquivCompatL with :I(A).
  - apply WhenOrdinalElem. assumption.
  - apply Ordinal.Inter.IsLowerBound; assumption.
Qed.

(* The infimum of a class is a lower-bound of its ordinals.                     *)
Proposition IsLowerBoundOrd : forall (A:Class) (a:U), On a ->
  A a -> inf A :<=: toClass a.
Proof.
  intros A a H1 H2. apply Incl.EquivCompatL with (inf (A :/\: On)).
  - apply EquivSym, InterOn.
  - apply IsLowerBound.
    + apply Inter2.IsInclR.
    + split; assumption.
Qed.

(* The infimum of a non-empty class of ordinals is the largest lower-bound.     *)
Proposition IsLargest : forall (A:Class) (a:U),
  A :<=: On                     ->
  A :<>: :0:                    ->
  (forall b, A b  -> a :<=: b)  ->
  toClass a :<=: inf A.
Proof.
  intros A a H1 H2 H3. apply Incl.EquivCompatR with :I(A).
  - apply WhenOrdinalElem. assumption.
  - apply Ordinal.Inter.IsLargest; assumption.
Qed.

(* The infimum of a class with an ordinal is the largest ordinal lower-bound.   *)
Proposition IsLargestOrd : forall (A:Class) (a:U),
  A :/\: On :<>: :0:                  ->
  (forall b, On b -> A b -> a :<=: b) ->
  toClass a :<=: inf A.
Proof.
  intros A a H1 H2. apply Incl.EquivCompatR with (inf (A :/\: On)).
  - apply EquivSym, InterOn.
  - apply IsLargest. 2: assumption.
    + apply Inter2.IsInclR.
    + intros b [H3 H4]. apply H2; assumption.
Qed.

(* ERROR: See after Definition 7.37 Exercises (4) page 45.                      *)
(* The set of the infimum of a non-empty class of ordinals belongs to the class.*)
Proposition IsIn : forall (A:Class) (a:U),
  A :<=: On         ->
  A :<>: :0:        ->
  IsSetOf (inf A) a ->
  A a.
Proof.
  intros A a H1 H2 H3.
  assert (exists b, A b /\ A :/\: toClass b :~: :0:) as H4. {
    apply HasEMinimal with On; try assumption. apply OnIsOrdinal. }
  destruct H4 as [b [H4 H5]].
  assert (forall c, A c -> b :<=: c) as H6. {
    intros c H6.
    assert (
      toClass b :~: toClass c \/
      toClass b :<: toClass c \/
      toClass c :<: toClass b) as H7. {
        apply OrdinalTotal; apply H1; assumption. }
    destruct H7 as [H7|[H7|H7]].
    - apply EqualToClass in H7. subst. apply InclRefl.
    - apply H7.
    - apply LessIsElem in H7.
      + exfalso. apply Class.Empty.Charac with c. apply H5. split; assumption.
      + apply H1. assumption.
      + apply H1. assumption. }
  assert (a = b) as H7. {
    apply ZF.Set.Incl.DoubleInclusion. split; intros x H7.
    - assert (inf A x) as H8. { apply H3. assumption. }
      apply H8. split. 1: assumption. apply H1. assumption.
    - apply H3. split.
      + intros c [H9 H10]. apply H6; assumption.
      + exists b. split. 1: assumption. apply H1. assumption. }
  subst. assumption.
Qed.

(* The set of the infimum of a class with an ordinal belongs to the class.      *)
Proposition IsInOrd : forall (A:Class) (a:U),
  A :/\: On :<>: :0:  ->
  IsSetOf (inf A) a   ->
  A a.
Proof.
  intros A a H1 H2.
  assert (On a) as H3. {
    apply Class.Ordinal.Core.EquivCompat with (inf A).
    apply EquivSym. assumption. apply IsOrdinal. }
  assert (IsSetOf (inf (A :/\: On)) a) as H4. {
    apply IsSetOf.EquivCompat with (inf A). 2: assumption.
    apply EquivSym, InterOn. }
  assert ((A :/\: On) a) as H5. {
    apply IsIn; try assumption. apply Inter2.IsInclR. }
  destruct H5 as [H5 _]. assumption.
Qed.

Proposition IsEMinimal : forall (A:Class) (a:U),
  A :<=: On   ->
  A :<>: :0:  ->
  IsSetOf (inf A) a <-> Minimal E A a.
Proof.
  intros A a H1 H2. split; intros H3.
  - assert (A a) as H4. { apply IsIn; assumption. }
    apply E.MinimalEA. split. 1: assumption.
    apply Class.Empty.HasNoElem. intros [b [H5 H6]].
    assert (a :<=: b) as H7. {
      apply Incl.EquivCompatL with (inf A).
      + apply EquivSym. assumption.
      + apply IsLowerBound; assumption. }
    apply NoElemLoop1 with b. apply H7. assumption.
  - apply E.MinimalEA in H3. destruct H3 as [H3 H4].
    apply Class.Incl.DoubleInclusion. split.
    + apply IsLargest; try assumption. intros b H5.
      assert (toClass a :~: toClass b \/
              toClass a :<: toClass b \/
              toClass b :<: toClass a) as H6. {
        apply OrdinalTotal; apply H1; assumption. }
      destruct H6 as [H6|[H6|H6]].
      * apply Incl.EquivCompatR with (toClass a). 1: assumption. apply InclRefl.
      * apply H6.
      * exfalso. apply Class.Empty.HasNoElem in H4. apply H4. exists b. split.
        1: assumption. apply Class.Ordinal.Core.LessIsElem;
        try assumption; apply H1; assumption.
    + apply IsLowerBound; assumption.
Qed.

Proposition WhenOrdinal : forall (A:Class) (a:U),
  Ordinal A                         ->
  On a                              ->
  A :\: toClass a :<>: :0:          ->
  IsSetOf (inf (A :\: toClass a)) a.
Proof.
  intros A a H1 H2 H3 x. split; intros H4.
  - assert (toClass a :<=: inf (A :\: toClass a)) as H5. {
      apply Inter.IsLargest.
      + apply Class.Inter2.IsInclR.
      + apply Class.Empty.HasElem in H3. destruct H3 as [b [H3 H5]].
        apply Class.Empty.HasElem. exists b. split.
        * split; assumption.
        * apply Class.Ordinal.Core.IsOrdinal with A; assumption.
      + intros b [[H5 H6] H7].
        assert (
          toClass a :~: toClass b \/
          toClass a :<: toClass b \/
          toClass b :<: toClass a) as H8. {
            apply OrdinalTotal; assumption. }
        destruct H8 as [H8|[H8|H8]].
        * apply EqualToClass in H8. subst. apply InclRefl.
        * apply H8.
        * apply LessIsElem in H8; try assumption. contradiction. }
    apply H5. assumption.
  - assert (inf (A :\: toClass a) :<=: toClass a) as H5. {
      apply Class.Empty.HasElem in H3. destruct H3 as [b [H3 H5]].
      apply Inter.IsLowerBound.
      + apply Class.Inter2.IsInclR.
      + split. 2: assumption. split. 2: apply NoElemLoop1.
        assert (
          toClass a :~: A \/
          toClass a :<: A \/
          A :<: toClass a) as H6. {
            apply OrdinalTotal; assumption. }
        destruct H6 as [H6|[H6|H6]].
        * exfalso. apply H5, H6. assumption.
        * apply Class.Ordinal.Core.LessIsElem; assumption.
        * exfalso. apply H5, H6. assumption. }
        apply H5. assumption.
Qed.
