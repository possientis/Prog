Require Import ZF.Axiom.Classic.
Require Import ZF.Class.Empty.
Require Import ZF.Class.Equiv.
Require Import ZF.Class.Incl.
Require Import ZF.Class.Rank.
Require Import ZF.Class.Small.
Require Import ZF.Set.Core.
Require Import ZF.Set.Incl.
Require Import ZF.Set.Ordinal.Core.
Require Import ZF.Set.Rank.

Module CEM := ZF.Class.Empty.
Module CRA := ZF.Class.Rank.

(* The class of elements of the class A with minmal rank.                       *)
Definition ofMinRank (A:Class) : Class := fun x =>
  A x /\ forall y, A y -> rank x :<=: rank y.


Proposition IsIncl : forall (A:Class), ofMinRank A :<=: A.
Proof.
  intros A x H1. apply H1.
Qed.

Proposition IsNotEmpty : forall (A:Class),
  A :<>: :0: -> ofMinRank A :<>: :0:.
Proof.
  intros A H1.
  apply CEM.HasElem in H1. destruct H1 as [a H1].
  remember (fun b => exists x, A x /\ b = rank x) as B eqn:H2.
  assert (B :<=: Ordinal) as H3. {
    intros b H3. rewrite H2 in H3. destruct H3 as [x [H3 H4]].
    subst. apply Rank.IsOrdinal. }
  assert (B :<>: :0:) as H4. {
    apply CEM.HasElem. exists (rank a). rewrite H2. exists a.
    split. 1: assumption. reflexivity. }
  assert (exists b, Ordinal b /\ B b /\ forall c, B c -> b :<=: c) as H5. {
    apply Core.HasMinimal; assumption. }
  destruct H5 as [b [H5 [H6 H7]]]. rewrite H2 in H6. destruct H6 as [x [H6 H8]].
  apply CEM.HasElem. exists x. split. 1: assumption.
  intros y H9. rewrite H8 in H7. apply H7. rewrite H2. exists y.
  split. 1: assumption. reflexivity.
Qed.

Proposition WhenZero : forall (A:Class),
  A :~: :0: -> ofMinRank A :~: :0:.
Proof.
  intros A H1.
  apply CEM.WhenIncl with A. 2: assumption. apply IsIncl.
Qed.

Proposition IsSmall : forall (A:Class), Small (ofMinRank A).
Proof.
  intros A.
  assert (A :~: :0: \/ A :<>: :0:) as H1. { apply LawExcludedMiddle. }
  destruct H1 as [H1|H1].
  - assert (ofMinRank A :~: :0:) as H2. {
      apply CEM.WhenIncl with A. 2: assumption. apply IsIncl. }
    apply Small.EquivCompat with :0:.
    + apply Equiv.Sym. assumption.
    + apply CEM.IsSmall.
  - apply CEM.HasElem in H1. destruct H1 as [a H1].
    apply CRA.IsSmall. exists (rank a). split.
    + apply Rank.IsOrdinal.
    + intros x [H4 H5]. apply H5. assumption.
Qed.
