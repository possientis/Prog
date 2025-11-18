Require Import ZF.Axiom.Classic.
Require Import ZF.Class.Empty.
Require Import ZF.Class.Equiv.
Require Import ZF.Class.Relation.Restrict.
Require Import ZF.Class.Small.
Require Import ZF.Set.Core.
Require Import ZF.Set.Empty.
Require Import ZF.Set.FromClass.
Require Import ZF.Set.Incl.
Require Import ZF.Set.OrdPair.
Require Import ZF.Set.Relation.Domain.
Require Import ZF.Set.Relation.Eval.
Require Import ZF.Set.Relation.Function.
Require Import ZF.Set.Relation.Functional.
Require Import ZF.Set.Relation.ImageOfClass.
Require Import ZF.Set.Relation.Range.
Require Import ZF.Set.Relation.Relation.
Require Import ZF.Set.Specify.

Export ZF.Notation.Pipe.

Definition restrict (f:U) (A:Class) : U := fromClass (toClass f :|: A)
  (Restrict.IsSmall' (toClass f) A (SetIsSmall f)).

(* Notation "f :|: A" := (restrict f A)                                         *)
Global Instance SetByClassPipe : Pipe U Class U := { pipe := restrict }.

Proposition ToClass : forall (A:Class) (f:U),
  toClass (f :|: A) :~: toClass f :|: A.
Proof.
  intros A f. apply FromClass.ToFromClass.
Qed.

Proposition EquivCompat : forall (A B:Class) (f:U),
  A :~: B -> f:|:A = f:|:B.
Proof.
  intros A B f H1.
  apply FromClass.EquivCompat, Restrict.EquivCompatR. assumption.
Qed.

Proposition Charac : forall (A:Class) (f x:U),
  x :< f:|:A <-> exists y z, x = :(y,z): /\ A y /\ :(y, z): :< f.
Proof.
  intros A f x. split; intros H1.
  - apply FromClass.Charac in H1. destruct H1 as [y [z [H1 [H2 H3]]]].
    exists y. exists z. split. 1: assumption. split; assumption.
  - destruct H1 as [y [z [H1 [H2 H3]]]]. apply FromClass.Charac.
    exists y. exists z. split. 1: assumption. split; assumption.
Qed.

Proposition Charac2 : forall (A:Class) (f y z:U),
  :(y,z): :< f:|:A <-> A y /\ :(y,z): :< f.
Proof.
  intros A f y z. split; intros H1.
  - apply Charac in H1. destruct H1 as [y' [z' [H1 [H2 H3]]]].
    apply OrdPair.WhenEqual in H1. destruct H1 as [H1 H4]. subst.
    split; assumption.
  - apply Charac. exists y. exists z. split. 2: assumption. reflexivity.
Qed.

(* The restriction of a set by a class is always a relation.                    *)
Proposition IsRelation : forall (A:Class) (f:U),
  Relation (f:|:A).
Proof.
  intros A f x H1. apply Charac in H1. destruct H1 as [y [z [H1 _]]].
  exists y. exists z. assumption.
Qed.

(* The restriction of a functional set is a functional set.                     *)
Proposition IsFunctional : forall (A:Class) (f:U),
  Functional f -> Functional (f:|:A).
Proof.
  intros A f H1 x y z H2 H3.
  apply Charac2 in H2. destruct H2 as [_ H2].
  apply Charac2 in H3. destruct H3 as [_ H3].
  apply H1 with x; assumption.
Qed.

Proposition IsFunction : forall (A:Class) (f:U),
  Functional f -> Function (f:|:A).
Proof.
  intros A f H1. split.
  - apply IsRelation.
  - apply IsFunctional. assumption.
Qed.

Proposition DomainOf : forall (A:Class) (f:U),
  domain (f:|:A) = {{ x :< domain f | A }}.
Proof.
  intros A f. apply DoubleInclusion. split; intros x H1.
  - apply Domain.Charac in H1. destruct H1 as [y H1].
    apply Charac2 in H1. destruct H1 as [H1 H2].
    apply Specify.Charac. split. 2: assumption.
    apply Domain.Charac. exists y. assumption.
  - apply Specify.Charac in H1. destruct H1 as [H1 H2].
    apply Domain.Charac in H1. destruct H1 as [y H1].
    apply Domain.Charac. exists y.
    apply Charac2. split; assumption.
Qed.

Proposition RangeOf : forall (A:Class) (f:U),
  range (f:|:A) = f:[A]:.
Proof.
  intros A f. apply DoubleInclusion. split; intros y H2.
  - apply Range.Charac in H2. destruct H2 as [x H2].
    apply Charac2 in H2. destruct H2 as [H2 H3].
    apply ImageOfClass.Charac. exists x. split; assumption.
  - apply ImageOfClass.Charac in H2. destruct H2 as [x [H2 H3]].
    apply Range.Charac. exists x. apply Charac2. split; assumption.
Qed.

Proposition RangeIsIncl : forall (A:Class) (f:U),
  range (f:|:A) :<=: range f.
Proof.
  intros A f y H1. apply Range.Charac in H1. destruct H1 as [x H1].
  apply Charac2 in H1. destruct H1 as [_ H1].
  apply Range.Charac. exists x. assumption.
Qed.

Proposition IsIncl : forall (A:Class) (f:U),
  f:|:A :<=: f.
Proof.
  intros A f x H1. apply Charac in H1. destruct H1 as [y [z [H1 [_ H2]]]].
  subst. assumption.
Qed.

Proposition TowerProperty : forall (A B:Class) (f:U),
  A :<=: B -> (f:|:B) :|: A = f:|:A.
Proof.
  intros A B f H1. apply DoubleInclusion. split; intros x H2.
  - apply Charac in H2. destruct H2 as [y [z [H2 [H3 H4]]]].
    apply Charac2 in H4. destruct H4 as [H4 H5].
    apply Charac. exists y. exists z. split. 1: assumption. split; assumption.
  - apply Charac in H2. destruct H2 as [y [z [H2 [H3 H4]]]].
    apply Charac. exists y. exists z. split. 1: assumption. split. 1: assumption.
    apply Charac2. split. 2: assumption. apply H1. assumption.
Qed.

Proposition Eval : forall (A:Class) (f x:U), Functional f ->
  A x -> (f:|:A)!x = f!x.
Proof.
  intros A f x H1 H2.
  assert (Functional (f:|:A)) as H3. { apply IsFunctional. assumption. }
  assert (x :< domain f \/ ~ x :< domain f) as H4. { apply LawExcludedMiddle. }
  remember (f!x) as y eqn:E. destruct H4 as [H4|H4].
  - assert (x :< domain (f:|:A)) as H5. {
      rewrite DomainOf. apply Specify.Charac. split; assumption. }
    apply Eval.Charac; try assumption. apply Charac2. split. 1: assumption.
    rewrite E. apply Eval.Satisfies; assumption.
  - assert (~ x :< domain (f:|:A)) as H5. {
      intros H5. apply Domain.Charac in H5. destruct H5 as [z H5].
      apply Charac2 in H5. destruct H5 as [H5 H6]. apply H4.
      apply Domain.Charac. exists z. assumption. }
    assert (y = :0:) as H6. {
      rewrite E. apply Eval.WhenNotInDomain. assumption. }
    rewrite H6. apply Eval.WhenNotInDomain. assumption.
Qed.

Proposition WhenEmpty : forall (A:Class) (f:U),
  A :~: :0: -> f:|:A = :0:.
Proof.
  intros A f H1. apply DoubleInclusion. split; intros x H2.
  - apply Charac in H2. destruct H2 as [y [z [_ [H3 _]]]].
    apply H1 in H3. contradiction.
  - apply Empty.Charac in H2. contradiction.
Qed.
