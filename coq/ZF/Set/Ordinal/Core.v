Require Import ZF.Class.
Require Import ZF.Class.Inter.
Require Import ZF.Class.Ordinal.
Require Import ZF.Class.Transitive2.
Require Import ZF.Class.Union.
Require Import ZF.Class.Empty.
Require Import ZF.Set.
Require Import ZF.Set.Foundation.
Require Import ZF.Set.Incl.
Require Import ZF.Set.Singleton.
Require Import ZF.Set.Union.
Require Import ZF.Set.Union2.

(* The class of all ordinals.                                                   *)
Definition Ordinal : Class := On.

(* An element of an ordinal is an ordinal.                                      *)
Proposition ElemIsOrdinal : forall (a b:U), Ordinal a ->
  b :< a -> Ordinal b.
Proof.
  intros a b H1 H2. apply Class.Ordinal.ElemIsOrdinal with (toClass a);
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
  intros a H1. apply (Class.Ordinal.StrictInclIsElem On); try assumption.
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
      apply Class.Ordinal.OrdinalTotal; assumption. }
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
    apply Class.Ordinal.ElemIsOrdinal with On. 
    apply OnIsOrdinal. apply H1. assumption. }
  split. 1: assumption. split. 1: assumption. intros b H6.
  assert (Ordinal b) as H7. { apply H1. assumption. }
  assert (a = b \/ a :< b \/ b :< a) as H8. { 
    apply OrdinalTotal; assumption. }
  apply EqualOrStrictIncl; try assumption. destruct H8 as [H8|[H8|H8]].
  - left. assumption.
  - right. assumption.
  - exfalso. apply Empty.Charac with b. apply H4. split; assumption.
Qed.

(* The max of two ordinals is equal to one of them.                             *)
Proposition MaxIsLeftOrRight : forall (a b:U), Ordinal a -> Ordinal b ->
  a :\/: b = a \/ a :\/: b = b.
Proof.
  intros a b H1 H2. assert (a :<=: b \/ b :<=: a) as H3. {
    apply InclOrIncl; assumption. }
  destruct H3 as [H3|H3].
  - apply Union2EqualIncl in H3. right. symmetry. assumption.
  - apply Union2EqualIncl in H3. left. symmetry. rewrite Union2Comm. assumption. 
Qed.

(* The max of two ordinals is an ordinal.                                       *)
Proposition MaxIsOrdinal : forall (a b:U), Ordinal a -> Ordinal b ->
  Ordinal (a :\/: b).
Proof.
  intros a b H1 H2. assert (a :\/: b = a \/ a :\/: b = b) as H3. {
    apply MaxIsLeftOrRight; assumption. }
  destruct H3 as [H3|H3]; rewrite H3; assumption.
Qed.

(* The union of an ordinal is an ordinal.                                       *)
Proposition UnionIsOrdinal : forall (a:U), Ordinal a ->
  Ordinal :U(a).
Proof.
  intros a H1. apply Class.Ordinal.EquivCompat with :U(toClass a).
  - apply UnionOfToClass.
  - apply Class.Ordinal.UnionIsOrdinal, OrdinalIsStrictSubclass. assumption.
Qed.

(* The union of an ordinal is an upper-bound ot its elements.                   *)
Proposition UnionIsUpperBound : forall (a b:U), Ordinal a -> 
  b :< a -> b :<=: :U(a). 
Proof.
  intros a b H1 H2. apply Incl.EquivCompatR with :U(toClass a).
  - apply UnionOfToClass.
  - apply Class.Ordinal.UnionIsUpperBound. 2: assumption.
    apply OrdinalIsStrictSubclass. assumption.
Qed.

(* The union of an ordinal is the smallest upper-bound.                         *)
Proposition UnionIsSmallestUpperBound : forall (a b:U), Ordinal a -> Ordinal b ->
  (forall c, c :< a -> c :<=: b) -> :U(a) :<=: b.
Proof.
  intros a b H1 H2 H3. apply Incl.EquivCompatL with :U(toClass a).
  - apply UnionOfToClass.
  - apply Class.Ordinal.UnionIsSmallestUpperBound; try assumption.
    apply OrdinalIsStrictSubclass. assumption. 
Qed.

Proposition UnionNotElemIsUnionEqual : forall (a:U), Ordinal a ->
  ~ :U(a) :< a <-> :U(a) = a.
Proof.
  intros a H1. split; intros H2.
  - apply DoubleInclusion. split.
    + apply UnionIsSmallestUpperBound; try assumption.
      intros c H3. apply ElemIsIncl; try assumption.
      apply ElemIsOrdinal with a; assumption.
    + assert (:U(a) :< a \/ a :<=: :U(a)) as H3. {
        apply ElemOrIncl. 2: assumption. apply UnionIsOrdinal. assumption. }
      destruct H3 as [H3|H3]. 1: contradiction. assumption.
  - intros H3. rewrite H2 in H3. apply NoElemLoop1 with a. assumption.
Qed.

