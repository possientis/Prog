Require Import ZF.Class.Equiv.
Require Import ZF.Class.Small.
Require Import ZF.Class.Truncate.
Require Import ZF.Set.Core.
Require Import ZF.Set.Empty.
Require Import ZF.Set.FromClass.
Require Import ZF.Set.Incl.

Definition truncate (A:Class) : U :=
  fromClass (Class.Truncate.truncate A) (Class.Truncate.IsSmall A).

Proposition Charac : forall (A:Class) (x:U),
  x :< truncate A <-> Small A /\ A x.
Proof.
  intros A x. split; intros H1.
  - apply FromClass.Charac in H1. assumption.
  - apply FromClass.Charac. assumption.
Qed.

Proposition EquivCompat : forall (A B:Class),
  A :~: B -> truncate A = truncate B.
Proof.
  intros A B H1.
  apply FromClass.EquivCompat, Class.Truncate.EquivCompat. assumption.
Qed.

Proposition WhenSmall : forall (A:Class),
  Small A -> toClass (truncate A) :~: A.
Proof.
  intros A H1. apply Equiv.Tran with (Class.Truncate.truncate A).
  - apply ToFromClass.
  - apply Class.Truncate.WhenSmall. assumption.
Qed.

Proposition WhenNotSmall : forall (A:Class),
  ~ Small A -> truncate A = :0:.
Proof.
  intros A H1. apply EqualToClass.
  apply Equiv.Tran with (Class.Truncate.truncate A).
  - apply ToFromClass.
  - apply Equiv.Tran with :0:.
    + apply Class.Truncate.WhenNotSmall. assumption.
    + apply Equiv.Sym, Empty.ToClass.
Qed.

Proposition WhenEmpty : forall (A:Class), A :~: :0: -> truncate A = :0:.
Proof.
  intros A H1. apply DoubleInclusion. split; intros x H2.
  - apply Charac in H2. destruct H2 as [_ H2]. apply H1 in H2. contradiction.
  - apply Empty.Charac in H2. contradiction.
Qed.
