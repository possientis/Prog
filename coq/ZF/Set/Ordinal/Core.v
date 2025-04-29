Require Import ZF.Class.Core.
Require Import ZF.Class.Inter2.
Require Import ZF.Class.Ordinal.Core.
Require Import ZF.Class.Ordinal.Transitive.
Require Import ZF.Class.Union.
Require Import ZF.Class.Empty.
Require Import ZF.Set.Core.
Require Import ZF.Set.Foundation.
Require Import ZF.Set.Incl.
Require Import ZF.Set.Less.
Require Import ZF.Set.Single.
Require Import ZF.Set.Union.

(* The class of all ordinals.                                                   *)
Definition Ordinal : Class := On.

(* An element of an ordinal is an ordinal.                                      *)
Proposition IsOrdinal : forall (a b:U), Ordinal a ->
  b :< a -> Ordinal b.
Proof.
  intros a b H1 H2. apply Class.Ordinal.Core.IsOrdinal with (toClass a);
  assumption.
Qed.

(* Strict inclusion and set membership coincide on ordinals.                    *)
Proposition LessIsElem : forall (a b:U), Ordinal a -> Ordinal b ->
  a :<: b <-> a :< b.
Proof.
  intros a b H1 H2. split; intros H3.
  - apply (LessIsElem (toClass b)); try assumption.
    apply LessFromClass. assumption.
  - apply LessFromClass, (LessIsElem (toClass b)); assumption.
Qed.

Proposition IfElemThenIncl : forall (a b:U), Ordinal a -> Ordinal b ->
  a :< b -> a :<=: b.
Proof.
  intros a b H1 H2 H3. apply LessIsElem in H3;
  try assumption. apply H3.
Qed.

(* An ordinal is a strict subclass of the class of ordinals.                    *)
Proposition IsLess : forall (a:U), Ordinal a ->
  toClass a :<: On.
Proof.
  intros a H1. apply (Class.Ordinal.Core.LessIsElem On); try assumption.
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
    - left. apply EqualFromClass. assumption.
    - right. left. apply LessIsElem; try assumption.
      apply LessFromClass. assumption.
    - right. right. apply LessIsElem; try assumption.
      apply LessFromClass. assumption.
Qed.

Proposition InclIsEqualOrElem : forall (a b:U),
  Ordinal a ->
  Ordinal b ->
  a :<=: b <-> a = b \/ a :< b.
Proof.
  intros a b H1 H2. split; intros H3.
  - apply Less.EqualOrLess in H3. destruct H3 as [H3|H3].
    + left. assumption.
    + right. apply LessIsElem; assumption.
  - destruct H3 as [H3|H3].
    + subst. apply InclRefl.
    + apply LessIsElem in H3; try assumption. apply H3.
Qed.

Proposition InclOrIncl : forall (a b:U), Ordinal a -> Ordinal b ->
  a :<=: b \/ b :<=: a.
Proof.
  intros a b H1 H2. assert (a = b \/ a :< b \/ b :< a) as H3. {
    apply OrdinalTotal; assumption. }
  destruct H3 as [H3|[H3|H3]].
  - subst. left. apply InclRefl.
  - left. apply LessIsElem in H3; try assumption. apply H3.
  - right. apply LessIsElem in H3; try assumption. apply H3.
Qed.

Proposition ElemOrIncl : forall (a b:U), Ordinal a -> Ordinal b ->
  a :< b \/ b :<=: a.
Proof.
  intros a b H1 H2. assert (a = b \/ a :< b \/ b :< a) as H3. {
    apply OrdinalTotal; assumption. }
  destruct H3 as [H3|[H3|H3]].
  - subst. right. apply InclRefl.
  - left. assumption.
  - right. apply IfElemThenIncl; assumption.
Qed.

Proposition InclElemTran : forall (a b c:U),
  Ordinal a ->
  Ordinal b ->
  Ordinal c ->
  a :<=: b  ->
  b :<   c  ->
  a :<   c.
Proof.
  intros a b c H1 H2 H3 H4 H5. apply LessIsElem; try assumption.
  apply Less.InclLessTran with b. 1: assumption.
  apply LessIsElem; assumption.
Qed.

Proposition ElemInclTran : forall (a b c:U),
  Ordinal a ->
  Ordinal b ->
  Ordinal c ->
  a :<   b  ->
  b :<=: c  ->
  a :<   c.
Proof.
  intros a b c H1 H2 H3 H4 H5. apply LessIsElem; try assumption.
  apply Less.LessInclTran with b. 2: assumption.
  apply LessIsElem; assumption.
Qed.

Proposition ElemElemTran : forall (a b c:U),
  Ordinal a ->
  Ordinal b ->
  Ordinal c ->
  a :< b  ->
  b :< c  ->
  a :< c.
Proof.
  intros a b c H1 H2 H3 H4 H5. apply InclElemTran with b; try assumption.
  apply IfElemThenIncl; assumption.
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
    apply Class.Ordinal.Core.IsOrdinal with On.
    apply OnIsOrdinal. apply H1. assumption. }
  split. 1: assumption. split. 1: assumption. intros b H6.
  assert (Ordinal b) as H7. { apply H1. assumption. }
  assert (a = b \/ a :< b \/ b :< a) as H8. {
    apply OrdinalTotal; assumption. }
  apply InclIsEqualOrElem; try assumption. destruct H8 as [H8|[H8|H8]].
  - left. assumption.
  - right. assumption.
  - exfalso. apply Class.Empty.Charac with b. apply H4. split; assumption.
Qed.
