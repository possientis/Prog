Require Import ZF.Axiom.Classic.
Require Import ZF.Class.Core.
Require Import ZF.Class.Ordinal.Core.
Require Import ZF.Class.Ordinal.Transitive.
Require Import ZF.Class.Union.
Require Import ZF.Set.Core.
Require Import ZF.Set.Foundation.
Require Import ZF.Set.Incl.
Require Import ZF.Set.Ordinal.Core.
Require Import ZF.Set.Ordinal.Union.
Require Import ZF.Set.Single.
Require Import ZF.Set.Union.
Require Import ZF.Set.Union2.

Definition succ (a:U) : U := a :\/: :{a}:.

(* The successor of an ordinal is an ordinal.                                   *)
Proposition SuccIsOrdinal : forall (a:U), Ordinal a ->
  Ordinal (succ a).
Proof.
  intros a H1. split.
  - intros x H2 y H3. apply Union2Charac in H2.
    apply Union2Charac. destruct H2 as [H2|H2].
    + left. destruct H1 as [H1 _]. specialize (H1 x H2 y). apply H1. assumption.
    + apply Single.Charac in H2. subst. left. assumption.
  - intros x y H2 H3. apply Union2Charac in H2. apply Union2Charac in H3.
    destruct H2 as [H2|H2]; destruct H3 as [H3|H3].
    + destruct H1 as [_ H1]. apply H1; assumption.
    + apply Single.Charac in H3. subst. right. left. assumption.
    + apply Single.Charac in H2. subst. right. right. assumption.
    + apply Single.Charac in H2. apply Single.Charac in H3.
      subst. left. apply eq_refl.
Qed.

(* The successor of the union of an ordinal is an ordinal.                      *)
Proposition SuccOfUnionIsOrdinal : forall (a:U), Ordinal a ->
  Ordinal (succ :U(a)).
Proof.
  intros a H1. apply SuccIsOrdinal, UnionOfOrdinalIsOrdinal. assumption.
Qed.

(* The union of the class of ordinals is the class of ordinals.                 *)
Proposition UnionOfOn : :U(On) :~: On.
Proof.
  apply Class.Incl.DoubleInclusion. split.
  - apply Class.Ordinal.Transitive.UnionIncl, OnIsOrdinal.
  - intros a H1. exists (a :\/: :{a}:). split.
    + apply Union2Charac. right. apply Single.In.
    + apply SuccIsOrdinal. assumption.
Qed.

(* A set (ordinal or not) belongs to its successor.                             *)
Proposition ElemSucc : forall (a:U), a :< succ a.
Proof.
  intros a. apply Union2Charac. right. apply Single.In.
Qed.

(* A set (ordinal or not) is a subset of its successor.                         *)
Proposition InclSucc : forall (a:U), a :<=: succ a.
Proof.
  intros a.  apply Union2InclL.
Qed.

(* The successor of a set is not equal to the set in question.                  *)
Proposition SuccNotEqual : forall (a:U), succ a <> a.
Proof.
  intros a H1. apply NoElemLoop1 with a. assert (a :< succ a) as H2. {
    apply ElemSucc. }
  rewrite H1 in H2. assumption.
Qed.

(* The successor operation is injective.                                        *)
Proposition SuccInjective : forall (a b:U),
  succ a = succ b -> a = b.
Proof.
  intros a b H1.
  assert (a :< succ b) as H2. { rewrite <- H1. apply ElemSucc. }
  assert (b :< succ a) as H3. { rewrite    H1. apply ElemSucc. }
  apply Union2Charac in H2. apply Union2Charac in H3.
  destruct H2 as [H2|H2]; destruct H3 as [H3|H3].
  - exfalso. apply NoElemLoop2 with a b. split; assumption.
  - apply Single.Charac in H3. subst. reflexivity.
  - apply Single.Charac in H2. assumption.
  - apply Single.Charac in H2. assumption.
Qed.

(* The sets a and b need not be ordinals.                                       *)
Proposition NothingInBetween : forall (a b:U),
  ~ (a :< b /\ b :< succ a).
Proof.
  intros a b [H1 H2]. apply Union2Charac in H2. destruct H2 as [H2|H2].
  - apply NoElemLoop2 with a b. split; assumption.
  - apply Single.Charac in H2. subst. apply NoElemLoop1 with a. assumption.
Qed.

(* The successor of the union of a set of ordinals is a strict 'upper-bound'.   *)
Proposition SuccOfUnionIsStrictUpperBound : forall (a b:U),
  toClass a :<=: On ->
  b :< a            ->
  b :< succ :U(a).
Proof.
  intros a b H1 H2. apply InclElemTran with :U(a).
  - apply H1. assumption.
  - apply UnionIsOrdinal. assumption.
  - apply SuccIsOrdinal, UnionIsOrdinal. assumption.
  - apply UnionIsUpperBound; assumption.
  - apply ElemSucc.
Qed.

(* The successor of the union of an ordinal is a strict upper-bound.            *)
Proposition SuccOfUnionOfOrdinalIsStrictUpperBound : forall (a b:U),
  Ordinal a         ->
  b :< a            ->
  b :< succ :U(a).
Proof.
  intros a b H1. apply SuccOfUnionIsStrictUpperBound.
  apply OrdinalIsStrictSubclass. assumption.
Qed.

(* An ordinal is a subset of the successor ot its union.                        *)
Proposition SuccOfUnionIsMore : forall (a:U), Ordinal a ->
  a :<=: succ :U(a).
Proof.
  intros a H1 b. apply SuccOfUnionOfOrdinalIsStrictUpperBound. assumption.
Qed.

(* An ordinal is either equal to its union, or to the successor thereof.        *)
Proposition UnionOrSuccOfUnion : forall (a:U), Ordinal a ->
  a = :U(a) \/ a = succ :U(a).
Proof.
  intros a H1. apply DoubleNegation. intros H2.
  apply NothingInBetween with :U(a) a. split.
  - apply StrictInclIsElem. 2: assumption.
    + apply UnionOfOrdinalIsOrdinal. assumption.
    + split.
      * apply UnionIsLess. assumption.
      * intros H3. apply H2. left. symmetry. assumption.
  - apply StrictInclIsElem. 1: assumption.
    + apply SuccOfUnionIsOrdinal. assumption.
    + split.
      * apply SuccOfUnionIsMore. assumption.
      * intros H3. apply H2. right. assumption.
Qed.

(* The union of the successor of an ordinal is the ordinal.                     *)
Proposition UnionOfSucc : forall (a:U), Ordinal a ->
  :U(succ a) = a.
Proof.
  intros a H1. apply DoubleInclusion. split; intros x H2.
  - apply Union.Charac in H2. destruct H2 as [y [H2 H3]].
    apply Union2Charac in H3. destruct H3 as [H3|H3].
    + destruct H1 as [H1 _]. specialize (H1 y H3). apply H1. assumption.
    + apply Single.Charac in H3. subst. assumption.
  - apply Union.Charac. exists a. split. 1: assumption.
    apply Union2Charac. right. apply Single.In.
Qed.

(* If an ordinal is equal to its union, it cannot be a successor ordinal.       *)
Proposition IfUnionThenNotSucc : forall (a b:U), Ordinal a -> Ordinal b ->
  a = :U(a) -> a <> succ b.
Proof.
  intros a b H1 H2 H3 H4. apply SuccNotEqual with a.
  assert (:U(succ b) = b) as H5. { apply UnionOfSucc. assumption. }
  rewrite <- H4 in H5. assert (a = b) as H6. { rewrite <- H5. assumption. }
  rewrite <- H6 in H4. symmetry. assumption.
Qed.
