Require Import ZF.Axiom.Classic.
Require Import ZF.Class.Bounded.
Require Import ZF.Class.Complement.
Require Import ZF.Class.Empty.
Require Import ZF.Class.Equiv.
Require Import ZF.Class.Complement.
Require Import ZF.Class.Incl.
Require Import ZF.Class.Inter2.
Require Import ZF.Class.Less.
Require Import ZF.Class.Proper.
Require Import ZF.Class.Relation.Converse.
Require Import ZF.Class.Relation.Functional.
Require Import ZF.Class.Relation.Image.
Require Import ZF.Class.Small.
Require Import ZF.Class.Union2.
Require Import ZF.Set.Core.
Require Import ZF.Set.OrdPair.

Require Import ZF.Notation.Diff.
Export ZF.Notation.Diff.

Definition diff (A B:Class) : Class := A :/\: :¬:B.

(* Notation "A :\: B" := (diff A B)                                             *)
Global Instance ClassDiff : Diff Class := { diff := diff }.

Proposition EquivCompat : forall (A B C D:Class),
  A :~: C -> B :~: D -> A :\: B :~: C :\: D.
Proof.
  intros A B C D H1 H2. apply Inter2.EquivCompat. 1: assumption.
  apply Complement.EquivCompat. assumption.
Qed.

Proposition EquivCompatL : forall (A B C:Class),
  A :~: C -> A :\: B :~: C :\: B.
Proof.
  intros A B C H1. apply EquivCompat.
  - assumption.
  - apply Equiv.Refl.
Qed.

Proposition EquivCompatR : forall (A B C:Class),
  B :~: C -> A :\: B :~: A :\: C.
Proof.
  intros A B C H1. apply EquivCompat.
  - apply Equiv.Refl.
  - assumption.
Qed.

Proposition InclCompat : forall (A B C D:Class),
  A :<=: C -> D :<=: B -> A :\: B :<=: C :\: D.
Proof.
  intros A B C D H1 H2. apply Inter2.InclCompat. 1: assumption.
  apply Complement.InclCompat. assumption.
Qed.

Proposition InclCompatL : forall (A B C:Class),
  A :<=: C -> A :\: B :<=: C :\: B.
Proof.
  intros A B C H1. apply InclCompat.
  - assumption.
  - apply Class.Incl.Refl.
Qed.

Proposition InclCompatR : forall (A B C:Class),
  C :<=: B -> A :\: B :<=: A :\: C.
Proof.
  intros A B C H1. apply InclCompat.
  - apply Class.Incl.Refl.
  - assumption.
Qed.

Proposition IsSmall : forall (A B:Class), Small A -> Small (A :\: B).
Proof.
  intros A B. apply Inter2.IsSmallL.
Qed.

Proposition WhenEmpty : forall (A B:Class),
  A :\: B  :~: :0: <-> A :<=: B.
Proof.
  intros A B. split; intros H1.
  - intros x H2. apply DoubleNegation. intros H3.
    apply Class.Empty.Charac with x, H1. split; assumption.
  - intros x. split; intros H2.
    + destruct H2 as [H2 H3].
      apply H1 in H2. contradiction.
    + apply Class.Empty.Charac in H2. contradiction.
Qed.

Proposition WhenNotEmpty : forall (A B:Class),
  A :\: B :<>: :0: -> A :<>: B.
Proof.
  intros A B H1 H2. apply Class.Empty.HasElem in H1.
  destruct H1 as [x [H1 H3]]. apply H3, H2. assumption.
Qed.

Proposition WhenIncl : forall (A B:Class),
  B :<=: A -> A :\: B :<>: :0: <-> A :<>: B.
Proof.
  intros A B H1. split; intros H2 H3.
  - apply Class.Empty.HasElem in H2. destruct H2 as [x [H2 H4]].
    apply H4, H3. assumption.
  - apply H2, DoubleInclusion. split. 2: assumption.
    intros x H4. apply DoubleNegation. intros H5. apply Class.Empty.Charac with x.
    apply H3. split; assumption.
Qed.

Proposition WhenLess : forall (A B:Class),
  B :<: A -> A :\: B :<>: :0:.
Proof.
  intros A B H1. apply Class.Empty.HasElem.
  apply Less.Exists in H1. destruct H1 as [_ H1]. assumption.
Qed.

Proposition UnionR : forall (A B C:Class),
  A :\: (B:\/:C) :~: (A:\:B) :/\: (A:\:C).
Proof.
  intros A B C x. split; intros H1.
  - destruct H1 as [H1 H2]. split; split.
    + assumption.
    + intros H3. apply H2. left. assumption.
    + assumption.
    + intros H3. apply H2. right. assumption.
  - destruct H1 as [H1 H2]. destruct H1 as [H1 H3]. destruct H2 as [_ H2]. split.
    + assumption.
    + intros H4. destruct H4 as [H4|H4]; contradiction.
Qed.

Proposition Image : forall (F A B:Class),
  Functional F^:-1: -> F:[A:\:B]: :~: F:[A]: :\: F:[B]:.
Proof.
  intros F A B H1 y. split; intros H2.
  - destruct H2 as [x [H2 H3]]. destruct H2 as [H2 H4]. split.
    + exists x. split; assumption.
    + intros [x' [H5 H6]].
      assert (x' = x) as H7. {
        apply Converse.WhenFunctional with F y; assumption. }
      subst. contradiction.
  - destruct H2 as [[x [H2 H3]] H4].
    exists x. split. 2: assumption. split.
    1: assumption. intros H5. apply H4. exists x. split; assumption.
Qed.

Proposition MinusASet : forall (A:Class) (a:U),
  Proper A -> A :\: toClass a :<>: :0:.
Proof.
  intros A a H1 H2. apply WhenEmpty in H2.
  assert (Small A) as H3. {
    apply Bounded.WhenSmaller with (toClass a). 1: assumption.
    apply SetIsSmall. }
  revert H3. assumption.
Qed.

