Require Import ZF.Axiom.Classic.
Require Import ZF.Class.Core.
Require Import ZF.Class.Complement.
Require Import ZF.Class.Diff.
Require Import ZF.Class.Empty.
Require Import ZF.Class.Incl.
Require Import ZF.Class.Inter2.
Require Import ZF.Class.Less.
Require Import ZF.Class.Order.E.
Require Import ZF.Class.Order.Founded.
Require Import ZF.Class.Order.Minimal.
Require Import ZF.Class.Order.Total.
Require Import ZF.Class.Order.WellFounded.
Require Import ZF.Class.Order.WellFoundedWellOrd.
Require Import ZF.Class.Order.WellOrdering.
Require Import ZF.Class.Ordinal.Transitive.
Require Import ZF.Class.Proper.
Require Import ZF.Class.Small.
Require Import ZF.Class.V.
Require Import ZF.Set.Core.
Require Import ZF.Set.Foundation.
Require Import ZF.Set.Incl.
Require Import ZF.Set.OrdPair.
Require Import ZF.Set.Single.
Require Import ZF.Set.Union2.

(* Predicate defining an ordinal class.                                         *)
Definition Ordinal (A:Class) : Prop := Transitive A /\ forall x y,
  A x -> A y -> x = y \/ x :< y \/ y :< x.

(* The class of all sets which are ordinals.                                    *)
Definition On : Class := fun x => Ordinal (toClass x).

Proposition ZeroIsOrdinal : Ordinal :0:.
Proof.
  split.
  - apply ZeroIsTransitive.
  - intros x y H1.  apply Class.Empty.Charac in H1. contradiction.
Qed.

(* Being an ordinal class is compatible with class equivalence.                 *)
Definition EquivCompat : forall (A B:Class),
  A :~: B -> Ordinal A -> Ordinal B.
Proof.
  intros A B H1 [H2 H3]. split.
  - apply Transitive.EquivCompat with A; assumption.
  - intros x y H4 H5. apply H3; apply H1; assumption.
Qed.

(* E is a total order on every ordinal class.                                   *)
Proposition EIsTotalOnOrdinals : forall (A:Class),
  Ordinal A -> Total E A.
Proof.
  intros A [H1 H2] x y H3 H4. specialize (H2 x y H3 H4). destruct H2 as [H2|[H2|H2]].
  - subst. left. reflexivity.
  - right. left. apply ECharac2. assumption.
  - right. right. apply ECharac2. assumption.
Qed.

(* E is a well-ordering on every ordinal class.                                 *)
Proposition EWellOrdersOrdinals : forall (A:Class),
  Ordinal A -> WellOrdering E A.
Proof.
  intros A H1. split.
  - apply FoundedIncl with V.
    + apply EIsFoundedOnV.
    + apply V.IsIncl.
  - apply EIsTotalOnOrdinals. assumption.
Qed.

(* Every non-empty sub-class of an ordinal class has an E-minimal element.      *)
Proposition HasEMinimal : forall (A B:Class),
  Ordinal A   ->
  B :<=: A    ->
  B :<>: :0:  ->
  exists x, B x /\ B :/\: toClass x :~: :0:.
Proof.
  intros A B H1 H2 H3.
  assert (exists x, Minimal E B x) as H4. { apply HasMinimal with A;
    try assumption. split.
    - apply WellFoundedIncl with V. apply EIsWellFoundedOnV.
      apply V.IsIncl.
    - apply EWellOrdersOrdinals. assumption. }
  destruct H4 as [x H4]. exists x. apply MinimalEA. assumption.
Qed.

(* An element of an ordinal class defines an ordinal class.                     *)
Proposition IsOrdinal : forall (A:Class) (a:U),
  Ordinal A -> A a -> Ordinal (toClass a).
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

(* A transitive strict subclass of an ordinal class is small.                   *)
Proposition TransitiveLessIsSmall : forall (A B:Class),
  Ordinal A    ->
  Transitive B ->
  B :<: A      ->
  Small B.
Proof.
  (* Let A and B be arbitrary classes. *)
  intros A B.

  (* We assume that A is an ordinal class. *)
  intros H1. assert (Ordinal A) as X. apply H1. clear X.

  (* We assume that B is a transitive class. *)
  intros H2. assert (Transitive B) as X. apply H2. clear X.

  (* We assume that B < A. *)
  intros H3. assert (B :<: A) as X. apply H3. clear X.

  (* We need to show that B is a small class. *)
  assert (Small B) as X. 2: apply X.

  (* In other words, we need to show the existence of a set b ... *)
  assert (exists b, forall x, x :< b <-> B x) as X. 2: apply X.

  (* We claim that the non-empty class A\B has an :<-minimal element. *)
  assert (exists b, (A :\: B) b /\ (A :\: B) :/\: toClass b :~: :0:) as H4. {
    apply HasEMinimal with A. 1: assumption.
    - apply Class.Inter2.InclL.
    - apply Diff.WhenLess. assumption. }

  (* So let b be such a set.  *)
  destruct H4 as [b [H4 H5]].

  (* Then b lies in the class A\B. *)
  assert ((A:\:B) b) as X. apply H4. clear X.

  (* and (A\B) /\ b = 0. *)
  assert ((A:\:B) :/\: toClass b :~: :0:) as X. apply H5. clear X.

  (* We claim the set b has the desired property. *)
  exists b.

  (* So given a set x *)
  intros x.

  (* We need to show the equivalence x :< b <-> B x. *)
  assert (x :< b <-> B x) as X. 2: apply X. split; intros H6.

  (* Proof of ->. *)
  - apply DoubleNegation. intros H7. apply Class.Empty.Charac with x, H5.
    split. 2: assumption. split. 2: assumption. destruct H1 as [H1 H8].
    apply (H1 b). 2: assumption. apply H4.

  (* Proof of <-. *)
  - assert (A b) as H7. { apply H4. }
    assert (A x) as H8. { apply H3. assumption. }
    destruct H1 as [H1 H9]. specialize (H9 b x H7 H8).
    destruct H9 as [H9|[H9|H9]].
    + subst. exfalso. apply H4. assumption.
    + exfalso. apply H4. apply (H2 x); assumption.
    + assumption.
Qed.

(* For a transitive set, belonging to an ordinal is being a strict subclass.    *)
Proposition WhenTransitiveLessIsElem : forall (A:Class) (a:U),
  Ordinal A               ->
  Transitive (toClass a)  ->
  toClass a :<: A <-> A a.
Proof.
  intros A a H1 H2. split; intros H3.
  - assert ( exists x,
     (A :\: toClass a) x /\
     (A :\: toClass a)  :/\: toClass x :~: :0:) as H4. {
     apply HasEMinimal with A. 1: assumption.
     - apply Class.Inter2.InclL.
     - apply Diff.WhenLess. assumption. }
    destruct H4 as [x [H4 H5]]. assert (A x) as H6. { apply H4. }
    assert (x = a) as H7. 2: { subst. assumption. }
    apply ZF.Set.Incl.DoubleInclusion. destruct H1 as [H1 H9]. split; intros u H7.
    + apply DoubleNegation. intros H8. apply Class.Empty.Charac with u, H5.
      split. 2: assumption. split. 2: assumption.
      apply (H1 x); assumption.
    + assert (A u) as H8. { apply H3. assumption. }
      specialize (H9 x u H6 H8). destruct H9 as [H9|[H9|H9]].
      * subst. exfalso. apply H4. assumption.
      * exfalso. apply H4. apply (H2 u); assumption.
      * assumption.
  - apply Transitive.IsLess. 2: assumption. apply H1.
Qed.

(* For an ordinal set, belonging to an ordinal is being a strict subclass.      *)
Proposition LessIsElem : forall (A:Class) (a:U),
  Ordinal A               ->
  Ordinal (toClass a)     ->
  toClass a :<: A <-> A a.
Proof.
  intros A a H1 [H2 _]. apply WhenTransitiveLessIsElem; assumption.
Qed.

(* A transitive subclass of an ordinal class is an ordinal class.               *)
Proposition TransitiveInclIsOrdinal : forall (A B:Class),
  Ordinal A    ->
  Transitive B ->
  B :<=: A     ->
  Ordinal B.
Proof.
  intros A B H1 H2 H3. split. 1: assumption.
  intros x y H4 H5. apply H1; apply H3; assumption.
Qed.

(* The intersection of two ordinal classes is an ordinal class.                 *)
Proposition InterIsOrdinal : forall (A B:Class),
  Ordinal A -> Ordinal B -> Ordinal (A :/\: B).
Proof.
  intros A B H1 H2. apply TransitiveInclIsOrdinal with A. 1: assumption.
  2: apply Class.Inter2.InclL. intros a [H3 H4].
  destruct H1 as [H1 _]. destruct H2 as [H2 _]. apply InclInter2.
  - apply H1. assumption.
  - apply H2. assumption.
Qed.

(* Two ordinal classes are equal or strictly ordered by inclusion,              *)
Proposition OrdinalTotal : forall (A B:Class),
  Ordinal A ->
  Ordinal B ->
  A :~: B \/ A :<: B \/ B :<: A.
Proof.
  intros A B H1 H2.
  assert (~(A:/\:B :<: A /\ A:/\:B :<: B)) as H3. {
    intros [H3 H4]. assert (Small (A:/\:B)) as H5. {
      apply TransitiveLessIsSmall with A; try assumption.
      apply InterIsOrdinal; assumption. }
    apply Small.IsSomeSet in H5. destruct H5 as [a H5].
    assert (Transitive (toClass a)) as H6. {
      apply Transitive.EquivCompat with (A:/\:B). 1: assumption.
      apply InterIsOrdinal; assumption. }
    assert (A a) as H7. {
      apply WhenTransitiveLessIsElem; try assumption.
      apply Less.EquivCompatL with (A:/\:B); assumption. }
    assert (B a) as H8. {
      apply WhenTransitiveLessIsElem; try assumption.
      apply Less.EquivCompatL with (A:/\:B); assumption. }
    apply NoElemLoop1 with a. apply H5. split; assumption. }
  assert (A:/\:B :~: A \/ A:/\:B :~: B) as H4. {
    apply DoubleNegation. intros H4. apply H3. split.
    - split. 1: apply Class.Inter2.InclL. intros H5. apply H4.
      left. assumption.
    - split. 1: apply Class.Inter2.InclR. intros H5. apply H4.
      right. assumption. }
  assert (A :~: B \/ A :<>: B) as H5. { apply LawExcludedMiddle. }
  destruct H5 as [H5|H5].
  - left. assumption.
  - right. destruct H4 as [H4|H4].
    + left. split. 2: assumption. apply IsInter2InclL, EquivSym. assumption.
    + right. split.
      * apply IsInter2InclR, EquivSym. assumption.
      * apply NotEquivSym. assumption.
Qed.

(* The class of ordinals is an ordinal class.                                   *)
Proposition OnIsOrdinal : Ordinal On.
Proof.
  split.
  - intros a H1 x H2. apply IsOrdinal with (toClass a); assumption.
  - intros a b H1 H2. assert (
      toClass a :~: toClass b \/
      toClass a :<: toClass b \/
      toClass b :<: toClass a) as H3. { apply OrdinalTotal; assumption. }
    destruct H3 as [H3|[H3|H3]].
    + left. apply EqualToClass. assumption.
    + right. left. apply (LessIsElem (toClass b)); assumption.
    + right. right. apply (LessIsElem (toClass a)); assumption.
Qed.

(* The class of ordinals is a proper class.                                     *)
Proposition OnIsProper : Proper On.
Proof.
  intros H1. apply Small.IsSomeSet in H1. destruct H1 as [a H1].
  apply NoElemLoop1 with a. apply H1. apply EquivCompat with On.
  1: assumption. apply OnIsOrdinal.
Qed.

(* Every ordinal class is the class of ordinals or a strict subclass thereof.   *)
Proposition IsLess : forall (A:Class),
  Ordinal A -> A :~: On \/ A :<: On.
Proof.
  intros A H1. assert (A :~: On \/ A :<: On \/ On :<: A) as H2. {
    apply OrdinalTotal. 1: assumption. apply OnIsOrdinal. }
  destruct H2 as [H2|[H2|H2]].
  - left. assumption.
  - right. assumption.
  - exfalso. apply OnIsProper.
    apply TransitiveLessIsSmall with A; try assumption.
    apply OnIsOrdinal.
Qed.

(* Every ordinal class is a subclass of the class of ordinals.                  *)
Proposition IsIncl : forall (A:Class),
  Ordinal A -> A :<=: On.
Proof.
  intros A H1. assert (A :~: On \/ A :<: On) as H2. {
    apply IsLess. assumption. }
  destruct H2 as [H2|H2].
  - apply Incl.EquivCompatL with On. apply EquivSym. 1: assumption.
    apply Class.Incl.InclRefl.
  - apply H2.
Qed.

(* Every ordinal class is small, unless it is the class of ordinals.            *)
Proposition IsSmall : forall (A:Class),
  Ordinal A -> A :~: On \/ Small A.
Proof.
  intros A H1. assert (A :~: On \/ A :<: On) as H2. {
    apply IsLess. assumption. }
  destruct H2 as [H2|H2].
  - left. assumption.
  - right. apply TransitiveLessIsSmall with On. 3: assumption.
    + apply OnIsOrdinal.
    + apply H1.
Qed.

(* Principle of transfinite induction.                                          *)
Proposition TransfiniteInduction : forall (A:Class),
  A :<=: On                                   ->
  (forall a, On a -> toClass a :<=: A -> A a) ->
  A :~: On.
Proof.
  intros A H1 H2. apply DoubleNegation. intros H3.
  assert (On :\: A :<>: :0:) as H4. { apply Diff.WhenLess. split; assumption. }
  assert (exists a, (On :\: A) a /\ (On :\: A) :/\: toClass a :~: :0:) as H5. {
    apply HasEMinimal with On. 3: assumption.
    - apply OnIsOrdinal.
    - apply Class.Inter2.InclL. }
  destruct H5 as [a [[H5 H6] H7]]. assert (toClass a :<: On) as H8. {
    apply LessIsElem; try assumption. apply OnIsOrdinal. }
  assert (toClass a :<=: A) as H9. {
    intros x H10. apply DoubleNegation. intros H11.
    apply Class.Empty.Charac with x, H7. split. 2: assumption. split. 2: assumption.
    apply IsOrdinal with (toClass a); assumption. }
  apply H6, H2; assumption.
Qed.

(* An element of an ordinal class is equal to its intersection with the class.  *)
Proposition ElemIsInter : forall (A:Class) (a:U),
  Ordinal A -> A a -> toClass a :~: toClass a :/\: A.
Proof.
  intros A a H1 H2. apply Class.Incl.DoubleInclusion. split.
  2: apply Class.Inter2.InclL. intros x H3. split. 1: assumption.
  destruct H1 as [H1 _]. specialize (H1 a H2 x). apply H1. assumption.
Qed.

Proposition Succ : forall (a:U), On a -> On (a :\/: :{a}:).
Proof.
  intros a H1. split.
  - intros x H2 y H3. apply Union2.Charac in H2.
    apply Union2.Charac. destruct H2 as [H2|H2].
    + left. destruct H1 as [H1 _]. specialize (H1 x H2 y). apply H1. assumption.
    + apply Single.Charac in H2. subst. left. assumption.
  - intros x y H2 H3. apply Union2.Charac in H2. apply Union2.Charac in H3.
    destruct H2 as [H2|H2]; destruct H3 as [H3|H3].
    + destruct H1 as [_ H1]. apply H1; assumption.
    + apply Single.Charac in H3. subst. right. left. assumption.
    + apply Single.Charac in H2. subst. right. right. assumption.
    + apply Single.Charac in H2. apply Single.Charac in H3.
      subst. left. apply eq_refl.
Qed.
