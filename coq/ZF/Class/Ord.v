Require Import ZF.Axiom.Classic.
Require Import ZF.Class.
Require Import ZF.Class.Diff.
Require Import ZF.Class.E.
Require Import ZF.Class.Empty.
Require Import ZF.Class.Founded.
Require Import ZF.Class.Incl.
Require Import ZF.Class.Inter.
Require Import ZF.Class.Minimal.
Require Import ZF.Class.Total.
Require Import ZF.Class.Tr.
Require Import ZF.Class.V.
Require Import ZF.Class.WellFounded.
Require Import ZF.Class.WellFoundedWellOrd.
Require Import ZF.Class.WellOrdering.
Require Import ZF.Set.
Require Import ZF.Set.Foundation.
Require Import ZF.Set.Incl.
Require Import ZF.Set.OrdPair.

(* Predicate defining an ordinal class.                                         *)
Definition Ord (A:Class) : Prop := Tr A /\ forall x y,
  A x -> A y -> x = y \/ x :< y \/ y :< x.

(* Being an ordinal class is compatible with class equivalence.                 *)
Definition OrdEquivCompat : forall (A B:Class),
  A :~: B -> Ord A -> Ord B.
Proof.
  intros A B H1 [H2 H3]. split.
  - apply TrEquivCompat with A; assumption.
  - intros x y H4 H5. apply H3; apply H1; assumption.
Qed.

(* E is a total order on every ordinal class.                                   *)
Proposition EIsTotalOnOrdinals : forall (A:Class),
  Ord A -> Total E A.
Proof.
  intros A [H1 H2] x y H3 H4. specialize (H2 x y H3 H4). destruct H2 as [H2|[H2|H2]].
  - subst. left. reflexivity.
  - right. left. apply ECharac2. assumption.
  - right. right. apply ECharac2. assumption.
Qed.

(* E is a well-ordering on every ordinal class.                                 *)
Proposition EWellOrdersOrdinals : forall (A:Class),
  Ord A -> WellOrdering E A.
Proof.
  intros A H1. split.
  - apply FoundedIncl with V.
    + apply EIsFoundedOnV.
    + apply VIsSuperClass.
  - apply EIsTotalOnOrdinals. assumption.
Qed.

(* Every non-empty sub-class of an ordinal class has an E-minimal element.      *)
Proposition HasEMinimal : forall (A B:Class),
  Ord A       ->
  B :<=: A    ->
  B :<>: :0:  ->
  exists x, B x /\ B :/\: toClass x :~: :0:.
Proof.
  intros A B H1 H2 H3.
  assert (exists x, Minimal E B x) as H4. { apply HasMinimal with A;
    try assumption. split.
    - apply WellFoundedIncl with V. apply EIsWellFoundedOnV.
      apply VIsSuperClass.
    - apply EWellOrdersOrdinals. assumption. }
  destruct H4 as [x H4]. exists x. apply MinimalEA. assumption.
Qed.

(* An element of an ordinal class defines an ordinal class.                     *)
Proposition ElemIsOrdinal : forall (A:Class) (a:U),
  Ord A -> A a -> Ord (toClass a).
Proof.
  intros A a [H1 H2] H3. split.
  - intros x H4 y H5.
    assert (A x) as H6. { apply (H1 a); assumption. }
    assert (A y) as H7. { apply (H1 x); assumption. }
    specialize (H2 a y H3 H7). destruct H2 as [H2|[H2|H2]].
    + subst. exfalso. apply NoElemLoop2 with x y. split; assumption.
    + exfalso. apply NoElemLoop3 with x a y. split. 1: assumption. split; assumption.
    + assumption.
  - intros x y H4 H5. apply H2; apply (H1 a); assumption.
Qed.

(* For a transitive set, belonging to an ordinal is being a strict subclass.    *)
Proposition WhenTrStrictInclIsElem : forall (A:Class) (a:U),
  Ord A          ->
  Tr (toClass a) ->
  toClass a :<: A <-> A a.
Proof.
  intros A a H1 H2. split; intros H3.
  - assert ( exists x,
     (A :\: toClass a) x /\
     (A :\: toClass a)  :/\: toClass x :~: :0:) as H4. {
     apply HasEMinimal with A. 1: assumption.
     - apply Inter.InclL.
     - apply Diff.WhenStrictIncl. assumption. }
    destruct H4 as [x [H4 H5]]. assert (A x) as H6. { apply H4. }
    assert (x = a) as H7. 2: { subst. assumption. }
    apply ZF.Set.Incl.DoubleInclusion. destruct H1 as [H1 H9]. split; intros u H7.
    + apply DoubleNegation. intros H8. apply (proj1 (Empty.Charac u)), H5.
      split. 2: assumption. split. 2: assumption.
      apply (H1 x); assumption.
    + assert (A u) as H8. { apply H3. assumption. }
      specialize (H9 x u H6 H8). destruct H9 as [H9|[H9|H9]].
      * subst. exfalso. apply H4. assumption.
      * exfalso. apply H4. apply (H2 u); assumption.
      * assumption.
  - apply ElemIsStrictSubClass. 2: assumption. apply H1.
Qed.

(* For an ordinal set, belonging to an ordinal is being a strict subclass.      *)
Proposition StrictInclIsElem : forall (A:Class) (a:U),
  Ord A           ->
  Ord (toClass a) ->
  toClass a :<: A <-> A a.
Proof.
  intros A a H1 [H2 _]. apply WhenTrStrictInclIsElem; assumption.
Qed.

(* A transitive subclass of an ordinal class is an ordinal class.               *)
Proposition TrSubClassIsOrd : forall (A B:Class),
  Ord A -> Tr B -> B :<=: A -> Ord B.
Proof.
  intros A B H1 H2 H3. split. 1: assumption.
  intros x y H4 H5. apply H1; apply H3; assumption.
Qed.

Proposition InterIsOrd : forall (A B:Class),
  Ord A -> Ord B -> Ord (A :/\: B).
Proof.
  intros A B H1 H2. apply TrSubClassIsOrd with A. 1: assumption.
  2: apply Inter.InclL. intros a [H3 H4].
Admitted.
