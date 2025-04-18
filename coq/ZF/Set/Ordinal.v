Require Import ZF.Class.
Require Import ZF.Class.Inter.
Require Import ZF.Class.Ordinal.
Require Import ZF.Class.Transitive2.
Require Import ZF.Class.Union.
Require Import ZF.Class.Empty.
Require Import ZF.Set.
Require Import ZF.Set.Incl.
Require Import ZF.Set.Singleton.
Require Import ZF.Set.Union2.

(* The class of all ordinals.                                                   *)
Definition Ordinal : Class := On.

(* Strict inclusion and set membership coincide on ordinals.                    *)
Proposition StrictInclIsElem : forall (a b:U), Ordinal a -> Ordinal b ->
  a :<: b <-> a :< b.
Proof.
  intros a b H1 H2. split; intros H3.
  - apply (StrictInclIsElem (toClass b)); try assumption.
    apply StrictInclFromClass. assumption.
  - apply StrictInclFromClass, (StrictInclIsElem (toClass b)); assumption.
Qed.

Proposition OrdinalIsStrictSubclass : forall (a:U), Ordinal a ->
  toClass a :<: Ordinal.
Proof.
  intros a H1. apply (Class.Ordinal.StrictInclIsElem On); try assumption.
  apply OnIsOrdinalClass.
Qed.

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

Proposition InclStricInclTran : forall (a b c:U),
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

Proposition StricInclInclTran : forall (a b c:U),
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

Proposition SuccIsOrdinal : forall (a:U), Ordinal a ->
  Ordinal (a :\/: :{a}:).
Proof.
  intros a H1. split.
  - intros x H2 y H3. apply Union2Charac in H2.
    apply Union2Charac. destruct H2 as [H2|H2].
    + left. destruct H1 as [H1 _]. specialize (H1 x H2 y). apply H1. assumption.
    + apply SingleCharac in H2. subst. left. assumption.
  - intros x y H2 H3. apply Union2Charac in H2. apply Union2Charac in H3.
    destruct H2 as [H2|H2]; destruct H3 as [H3|H3].
    + destruct H1 as [_ H1]. apply H1; assumption.
    + apply SingleCharac in H3. subst. right. left. assumption.
    + apply SingleCharac in H2. subst. right. right. assumption.
    + apply SingleCharac in H2. apply SingleCharac in H3. 
      subst. left. apply eq_refl.
Qed.

Proposition HasMinimal : forall (A:Class),
  A :<=: On   ->
  A :<>: :0:  ->
  exists a, 
    Ordinal a /\ 
    A a       /\
    forall b, Ordinal b -> A b -> a :<=: b.
Proof.
  intros A H1 H2.
  assert (exists a, A a /\ A :/\: toClass a :~: :0:) as H3. {
    apply HasEMinimal with On; try assumption. apply OnIsOrdinalClass. }
  destruct H3 as [a [H3 H4]]. exists a. assert (Ordinal a) as H5. {
    apply ElemIsOrdinal with On. apply OnIsOrdinalClass. apply H1. assumption. }
  split. 1: assumption. split. 1: assumption. intros b H6 H7.
  assert (a = b \/ a :< b \/ b :< a) as H8. { 
    apply OrdinalTotal; assumption. }
  apply EqualOrStrictIncl; try assumption. destruct H8 as [H8|[H8|H8]].
  - left. assumption.
  - right. assumption.
  - exfalso. apply Empty.Charac with b. apply H4. split; assumption.
Qed.

Proposition UnionOfOn : :U(On) :~: On.
Proof.
  apply Class.Incl.DoubleInclusion. split.
  - apply Transitive2.UnionIncl, OnIsOrdinalClass.
  - intros a H1. exists (a :\/: :{a}:). split.
    + apply Union2Charac. right. apply SingleIn.
    + apply SuccIsOrdinal. assumption.
Qed.

Proposition MaxIsLeftOrRight : forall (a b:U), Ordinal a -> Ordinal b ->
  a :\/: b = a \/ a :\/: b = b.
Proof.
  intros a b H1 H2. assert (a :<=: b \/ b :<=: a) as H3. {
    apply InclOrIncl; assumption. }
  destruct H3 as [H3|H3].
  - apply Union2EqualIncl in H3. right. symmetry. assumption.
  - apply Union2EqualIncl in H3. left. symmetry. rewrite Union2Comm. assumption. 
Qed.

Proposition MaxIsOrdinal : forall (a b:U), Ordinal a -> Ordinal b ->
  Ordinal (a :\/: b).
Proof.
  intros a b H1 H2. assert (a :\/: b = a \/ a :\/: b = b) as H3. {
    apply MaxIsLeftOrRight; assumption. }
  destruct H3 as [H3|H3]; rewrite H3; assumption.
Qed.


