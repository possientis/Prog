Require Import ZF.Class.Equiv.
Require Import ZF.Class.Ordinal.Core.
Require Import ZF.Class.Ordinal.Transitive.
Require Import ZF.Class.Union.
Require Import ZF.Set.Core.
Require Import ZF.Set.Empty.
Require Import ZF.Set.Foundation.
Require Import ZF.Set.Incl.
Require Import ZF.Set.Ordinal.Core.
Require Import ZF.Set.Ordinal.UnionOf.
Require Import ZF.Set.Single.
Require Import ZF.Set.Union.
Require Import ZF.Set.Union2.

Module COC := ZF.Class.Ordinal.Core.

Definition succ (a:U) : U := a :\/: :{a}:.

Definition Successor (a:U) : Prop := Ordinal a /\ exists b, a = succ b.


Definition Charac : forall (a x:U),
  x :< succ a <-> x = a \/ x :< a.
Proof.
  intros a x. split; intros H1.
  - apply Union2.Charac in H1. destruct H1 as [H1|H1].
    + right. assumption.
    + apply Single.Charac in H1. left. assumption.
  - destruct H1 as [H1|H1]; apply Union2.Charac.
    + right. apply Single.Charac. assumption.
    + left. assumption.
Qed.

(* A set (ordinal or not) belongs to its successor.                             *)
Proposition IsIn : forall (a:U), a :< succ a.
Proof.
  intros a. apply Union2.Charac. right. apply Single.IsIn.
Qed.

(* A successor is not the empty set.                                            *)
Proposition NotZero : forall (a:U), succ a <> :0:.
Proof.
  intros a H1. apply Empty.Charac with a. rewrite <- H1. apply IsIn.
Qed.

Proposition IsNotZero : forall (a:U), Successor a -> a <> :0:.
Proof.
  intros a [H1 [b H2]]. subst. apply NotZero.
Qed.

(* A set (ordinal or not) is a subset of its successor.                         *)
Proposition IsIncl : forall (a:U), a :<=: succ a.
Proof.
  intros a.  apply Union2.InclL.
Qed.

(* The successor of an ordinal is an ordinal.                                   *)
Proposition IsOrdinal : forall (a:U), Ordinal a ->
  Ordinal (succ a).
Proof.
  apply COC.Succ.
Qed.

Proposition IsSuccessor : forall (a:U), Ordinal a ->
  Successor (succ a).
Proof.
  intros a H1. split.
  - apply IsOrdinal. assumption.
  - exists a. reflexivity.
Qed.

Proposition HasZero : forall (a:U), Ordinal a -> :0: :< succ a.
Proof.
  intros a H1. apply Core.HasZero.
  - apply IsOrdinal. assumption.
  - apply NotZero.
Qed.

(* The successor operation is injective.                                        *)
Proposition Injective : forall (a b:U),
  succ a = succ b -> a = b.
Proof.
  intros a b H1.
  assert (a :< succ b) as H2. { rewrite <- H1. apply IsIn. }
  assert (b :< succ a) as H3. { rewrite    H1. apply IsIn. }
  apply Union2.Charac in H2. apply Union2.Charac in H3.
  destruct H2 as [H2|H2]; destruct H3 as [H3|H3].
  - exfalso. apply NoElemLoop2 with a b. split; assumption.
  - apply Single.Charac in H3. subst. reflexivity.
  - apply Single.Charac in H2. assumption.
  - apply Single.Charac in H2. assumption.
Qed.

(* The sets a and b need not be ordinals.                                       *)
Proposition NoInBetween : forall (a b:U),
  ~ (a :< b /\ b :< succ a).
Proof.
  intros a b [H1 H2]. apply Union2.Charac in H2. destruct H2 as [H2|H2].
  - apply NoElemLoop2 with a b. split; assumption.
  - apply Single.Charac in H2. subst. apply NoElemLoop1 with a. assumption.
Qed.

Proposition InBetween : forall (a b:U), Ordinal b ->
  a :< b -> b :<=: succ a -> b = succ a.
Proof.
  intros a b H1 H2 H3.
  apply DoubleInclusion. split. 1: assumption.
  intros x H4. apply Charac in H4. destruct H4 as [H4|H4].
  - subst. assumption.
  - assert (Ordinal a) as H5. { apply Core.IsOrdinal with b; assumption. }
    assert (Ordinal x) as H6. { apply Core.IsOrdinal with a; assumption. }
    apply Core.ElemElemTran with a; assumption.
Qed.

Proposition IsOrdinalRev : forall (a:U),
  Ordinal (succ a) -> Ordinal a.
Proof.
  intros a H1. apply Core.IsOrdinal with (succ a). 1: assumption. apply IsIn.
Qed.

Proposition HasZero' : forall (a:U), Successor a -> :0: :< a.
Proof.
  intros a [H1 [b H2]]. subst. apply HasZero, IsOrdinalRev. assumption.
Qed.

(* The successor operation is compatible with set inclusion for ordinals.       *)
Proposition InclCompat : forall (a b:U), Ordinal a -> Ordinal b ->
  a :<=: b -> succ a :<=: succ b.
Proof.
  intros a b H1 H2 H3 c H4.
  - apply Union2.Charac in H4. apply Union2.Charac.
    destruct H4 as [H4|H4].
    + left. apply H3. assumption.
    + apply Single.Charac in H4. subst.
      apply EqualOrElem in H3; try assumption. destruct H3 as [H3|H3].
      * subst. right. apply Single.IsIn.
      * left. assumption.
Qed.

Proposition InclCompatRev : forall (a b:U), Ordinal a -> Ordinal b ->
  succ a :<=: succ b -> a :<=: b.
Proof.
  intros a b H1 H2 H3 c H4. assert (Ordinal c) as H5. {
    apply Core.IsOrdinal with a; assumption. }
  assert (c :< b \/ b :<=: c) as H6. { apply ElemOrIncl; assumption. }
  destruct H6 as [H6|H6]. 1: assumption.
  exfalso. apply NoInBetween with b a. split.
  + apply InclElemTran with c; assumption.
  + apply H3, IsIn.
Qed.

Proposition ElemCompat : forall (a b:U), Ordinal a -> Ordinal b ->
  a :< b -> succ a :< succ b.
Proof.
  intros a b H1 H2 H3. apply LessIsElem.
  - apply IsOrdinal. assumption.
  - apply IsOrdinal. assumption.
  - apply LessIsElem in H3; try assumption. split.
    + apply InclCompat; try assumption. apply H3.
    + destruct H3 as [H3 H4]. intros H5. apply H4.
      apply Injective. assumption.
Qed.

Proposition ElemCompatRev : forall (a b:U), Ordinal a -> Ordinal b ->
  succ a :< succ b -> a :< b.
Proof.
  intros a b H1 H2 H3. assert (a :< b \/ b :<=: a) as H4. {
    apply ElemOrIncl; assumption. }
  destruct H4 as [H4|H4]. 1: assumption.
  exfalso. apply NoElemLoop1 with (succ a).
  apply ElemInclTran with (succ b); try assumption.
  - apply IsOrdinal. assumption.
  - apply IsOrdinal. assumption.
  - apply IsOrdinal. assumption.
  - apply InclCompat; assumption.
Qed.

Proposition ElemIsIncl : forall (a b:U), Ordinal a -> Ordinal b ->
  a :< b <-> succ a :<=: b.
Proof.
  intros a b H1 H2. split.
  - intros H3 c H4. apply Union2.Charac in H4. destruct H4 as [H4|H4].
    + apply ElemInclTran with a; try assumption.
      * apply Core.IsOrdinal with a; assumption.
      * apply LessIsElem in H3; try assumption. apply H3.
    + apply Single.Charac in H4. subst. assumption.
  - intros H3. assert (a :< b \/ b :<=: a) as H4. {
      apply ElemOrIncl; assumption. }
    destruct H4 as [H4|H4]. 1: assumption.
    exfalso. apply NoElemLoop1 with a.
    apply H4, H3, IsIn.
Qed.

Proposition InclIsElem : forall (a b:U), Ordinal a -> Ordinal b ->
  a :<=: b <-> a :< succ b.
Proof.
  intros a b H1 H2. split; intros H3.
  - apply Core.InclElemTran with b; try assumption.
    + apply IsOrdinal. assumption.
    + apply IsIn.
  - apply Charac in H3. destruct H3 as [H3|H3].
    + subst. apply Incl.Refl.
    + apply Core.ElemIsIncl; assumption.
Qed.

(* The successor of a set is not equal to the set in question.                  *)
Proposition NotEqual : forall (a:U), succ a <> a.
Proof.
  intros a H1. apply NoElemLoop1 with a. assert (a :< succ a) as H2. {
    apply IsIn. }
  rewrite H1 in H2. assumption.
Qed.

(* The union of the successor of an ordinal is the ordinal.                     *)
Proposition UnionOf : forall (a:U), Ordinal a ->
  :U(succ a) = a.
Proof.
  intros a H1. apply DoubleInclusion. split; intros x H2.
  - apply Union.Charac in H2. destruct H2 as [y [H2 H3]].
    apply Union2.Charac in H3. destruct H3 as [H3|H3].
    + destruct H1 as [H1 _]. specialize (H1 y H3). apply H1. assumption.
    + apply Single.Charac in H3. subst. assumption.
  - apply Union.Charac. exists a. split. 1: assumption.
    apply Union2.Charac. right. apply Single.IsIn.
Qed.

(* If an ordinal is equal to its union, it cannot be a successor ordinal.       *)
Proposition IfUnionThenNotSucc : forall (a b:U), Ordinal a -> Ordinal b ->
  a = :U(a) -> a <> succ b.
Proof.
  intros a b H1 H2 H3 H4. apply NotEqual with a.
  assert (:U(succ b) = b) as H5. { apply UnionOf. assumption. }
  rewrite <- H4 in H5. assert (a = b) as H6. { rewrite <- H5. assumption. }
  rewrite <- H6 in H4. symmetry. assumption.
Qed.

(* An ordinal is a successor iff it is the successor of its union.              *)
Proposition OfUnion : forall (a:U), Ordinal a ->
  Successor a <-> succ :U(a) = a.
Proof.
  intros a H1. split; intros H2.
  - destruct H2 as [H2 [b H3]]. subst.
    assert (Ordinal b) as H4. { apply IsOrdinalRev. assumption. }
    rewrite UnionOf. 2: assumption. reflexivity.
  - split. 1: assumption. exists :U(a). symmetry. assumption.
Qed.

