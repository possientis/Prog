Require Import ZF.Axiom.Classic.
Require Import ZF.Class.
Require Import ZF.Class.Irreflexive.
Require Import ZF.Class.StrictOrd.
Require Import ZF.Class.Transitive.
Require Import ZF.Class.Total.
Require Import ZF.Set.
Require Import ZF.Set.OrdPair.

(* Predicate expressing the fact that R is a strict total order class on A.     *)
Definition StrictTotalOrd (R A:Class) : Prop := StrictOrd R A /\ Total R A.

Proposition StrictTotalOrdIsStrictOrd : forall (R A:Class),
  StrictTotalOrd R A -> StrictOrd R A.
Proof.
  intros R A H1. apply H1.
Qed.

Proposition StrictTotalOrdIsTotal : forall (R A:Class),
  StrictTotalOrd R A -> Total R A.
Proof.
  intros R A H1. apply H1.
Qed.

Proposition StrictTotalOrdIsIrreflexive : forall (R A:Class),
  StrictTotalOrd R A -> Irreflexive R A.
Proof.
  intros R A H1.
  apply StrictOrdIsIrreflexive, StrictTotalOrdIsStrictOrd.
  assumption.
Qed.

Proposition StrictTotalOrdIsTransitive : forall (R A:Class),
  StrictTotalOrd R A -> Transitive R A.
Proof.
  intros R A H1.
  apply StrictOrdIsTransitive, StrictTotalOrdIsStrictOrd.
  assumption.
Qed.

Proposition StrictTotalOrdWhenSatisfied : forall (R A:Class) (x y:U),
  StrictTotalOrd R A ->
  A x                ->
  A y                ->
  R :(x,y): <-> ~ (x = y \/ R :(y,x):).
Proof.
  intros R A x y H1 H2 H3. split; intros H4.
  - intros H5. destruct H5 as [H5|H5].
    + subst. apply StrictTotalOrdIsIrreflexive in H1.
      revert H4. apply H1. assumption.
    + assert (R :(x,x):) as H6. {
        apply StrictTotalOrdIsTransitive in H1. apply H1 with y; assumption.
      }
     apply StrictTotalOrdIsIrreflexive in H1. revert H6. apply H1. assumption.
  - apply DoubleNegation. intros H5. apply StrictTotalOrdIsTotal in H1.
    destruct (H1 x y H2 H3) as [H7|[H7|H7]].
    + apply H4. left. assumption.
    + contradiction.
    + apply H4. right. assumption.
Qed.

Proposition StrictTotalOrdSuffice : forall (R A:Class),
  Transitive R A ->
  (forall x y, A x -> A y -> R :(x,y): <-> ~ (x = y \/ R :(y,x):)) ->
  StrictTotalOrd R A.
Proof.
  intros R A H1 H2. split.
  - split. 2: assumption. intros x H3 H4.
    apply (H2 _ _ H3 H3) in H4. apply H4. left. reflexivity.
  - intros x y H3 H4. specialize (H2 _ _ H3 H4).
    assert (x = y \/ x <> y) as H5. apply LawExcludedMiddle.
    destruct H5 as [H5|H5]. 1: { left. assumption. }
    assert (R :(y,x): \/ ~ R :(y,x):) as H6. apply LawExcludedMiddle.
    destruct H6 as [H6|H6]. 1: { right. right. assumption. }
    right. left. apply H2. intros [H7|H7].
    + apply H5. assumption.
    + apply H6. assumption.
Qed.
