Require Import ZF.Class.Core.
Require Import ZF.Class.Inter.
Require Import ZF.Class.Ordinal.Core.
Require Import ZF.Class.Ordinal.Transitive.
Require Import ZF.Class.Union.
Require Import ZF.Class.Empty.
Require Import ZF.Set.Core.
Require Import ZF.Set.Foundation.
Require Import ZF.Set.Incl.
Require Import ZF.Set.Single.
Require Import ZF.Set.Union.

(* The class of all ordinals.                                                   *)
Definition Ordinal : Class := On.

(* An element of an ordinal is an ordinal.                                      *)
Proposition ElemIsOrdinal : forall (a b:U), Ordinal a ->
  b :< a -> Ordinal b.
Proof.
  intros a b H1 H2. apply Class.Ordinal.Core.ElemIsOrdinal with (toClass a);
  assumption.
Qed.

(* Strict inclusion and set membership coincide on ordinals.                    *)
Proposition StrictInclIsElem : forall (a b:U), Ordinal a -> Ordinal b ->
  a :<: b <-> a :< b.
Proof.
  intros a b H1 H2. split; intros H3.
  - apply (StrictInclIsElem (toClass b)); try assumption.
    apply StrictInclFromClass. assumption.
  - apply StrictInclFromClass, (StrictInclIsElem (toClass b)); assumption.
Qed.

Proposition ElemIsIncl : forall (a b:U), Ordinal a -> Ordinal b ->
  a :< b -> a :<=: b.
Proof.
  intros a b H1 H2 H3. apply StrictInclIsElem in H3;
  try assumption. apply H3.
Qed.

(* An ordinal is a strict subclass of the class of ordinals.                    *)
Proposition OrdinalIsStrictSubclass : forall (a:U), Ordinal a ->
  toClass a :<: On.
Proof.
  intros a H1. apply (Class.Ordinal.Core.StrictInclIsElem On); try assumption.
  apply OnIsOrdinal.
Qed.

(* Ordinals are totally ordered by set membership.                              *)
Proposition OrdinalTotal : forall (a b:U), Ordinal a -> Ordinal b ->
  a = b \/ a :< b \/ b :< a.
Proof.
  intros a b H1 H2. assert (
    toClass a :~: toClass b \/
    toClass a :<: toClass b \/
    toClass b :<: toClass a) as H3. {
      apply Class.Ordinal.Core.OrdinalTotal; assumption. }
    destruct H3 as [H3|[H3|H3]].
    - left. apply EquivSetEqual. assumption.
    - right. left. apply StrictInclIsElem; try assumption.
      apply StrictInclFromClass. assumption.
    - right. right. apply StrictInclIsElem; try assumption.
      apply StrictInclFromClass. assumption.
Qed.

Proposition EqualOrStrictIncl : forall (a b:U), Ordinal a -> Ordinal b ->
  a :<=: b <-> a = b \/ a :< b.
Proof.
  intros a b H1 H2. split; intros H3.
  - apply Incl.EqualOrStrictIncl in H3. destruct H3 as [H3|H3].
    + left. assumption.
    + right. apply StrictInclIsElem; assumption.
  - destruct H3 as [H3|H3].
    + subst. apply InclRefl.
    + apply StrictInclIsElem in H3; try assumption. apply H3.
Qed.

Proposition InclOrIncl : forall (a b:U), Ordinal a -> Ordinal b ->
  a :<=: b \/ b :<=: a.
Proof.
  intros a b H1 H2. assert (a = b \/ a :< b \/ b :< a) as H3. {
    apply OrdinalTotal; assumption. }
  destruct H3 as [H3|[H3|H3]].
  - subst. left. apply InclRefl.
  - left. apply StrictInclIsElem in H3; try assumption. apply H3.
  - right. apply StrictInclIsElem in H3; try assumption. apply H3.
Qed.

Proposition ElemOrIncl : forall (a b:U), Ordinal a -> Ordinal b ->
  a :< b \/ b :<=: a.
Proof.
  intros a b H1 H2. assert (a = b \/ a :< b \/ b :< a) as H3. {
    apply OrdinalTotal; assumption. }
  destruct H3 as [H3|[H3|H3]].
  - subst. right. apply InclRefl.
  - left. assumption.
  - right. apply ElemIsIncl; assumption.
Qed.

Proposition InclElemTran : forall (a b c:U),
  Ordinal a ->
  Ordinal b ->
  Ordinal c ->
  a :<=: b  ->
  b :<   c  ->
  a :<   c.
Proof.
  intros a b c H1 H2 H3 H4 H5. apply StrictInclIsElem; try assumption.
  apply Incl.InclStrictInclTran with b. 1: assumption.
  apply StrictInclIsElem; assumption.
Qed.

Proposition ElemInclTran : forall (a b c:U),
  Ordinal a ->
  Ordinal b ->
  Ordinal c ->
  a :<   b  ->
  b :<=: c  ->
  a :<   c.
Proof.
  intros a b c H1 H2 H3 H4 H5. apply StrictInclIsElem; try assumption.
  apply Incl.StrictInclInclTran with b. 2: assumption.
  apply StrictInclIsElem; assumption.
Qed.

(* An non-empty class of ordinals has a minimal ordinal.                        *)
Proposition HasMinimal : forall (A:Class),
  A :<=: On   ->
  A :<>: :0:  ->
  exists a,
    Ordinal a /\
    A a       /\
    forall b, A b -> a :<=: b.
Proof.
  intros A H1 H2.
  assert (exists a, A a /\ A :/\: toClass a :~: :0:) as H3. {
    apply HasEMinimal with On; try assumption. apply OnIsOrdinal. }
  destruct H3 as [a [H3 H4]]. exists a. assert (Ordinal a) as H5. {
    apply Class.Ordinal.Core.ElemIsOrdinal with On.
    apply OnIsOrdinal. apply H1. assumption. }
  split. 1: assumption. split. 1: assumption. intros b H6.
  assert (Ordinal b) as H7. { apply H1. assumption. }
  assert (a = b \/ a :< b \/ b :< a) as H8. {
    apply OrdinalTotal; assumption. }
  apply EqualOrStrictIncl; try assumption. destruct H8 as [H8|[H8|H8]].
  - left. assumption.
  - right. assumption.
  - exfalso. apply Class.Empty.Charac with b. apply H4. split; assumption.
Qed.
