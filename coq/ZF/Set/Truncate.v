Require Import ZF.Axiom.Classic.
Require Import ZF.Class.Incl.
Require Import ZF.Class.Equiv.
Require Import ZF.Class.Small.
Require Import ZF.Class.Truncate.
Require Import ZF.Set.Core.
Require Import ZF.Set.Empty.
Require Import ZF.Set.FromClass.
Require Import ZF.Set.Incl.

Definition truncate (A:Class) : U :=
  fromClass (Class.Truncate.truncate A) (Class.Truncate.IsSmall A).

(* x belongs to truncate(A) iff A is small and x belongs to A.                  *)
Proposition Charac : forall (A:Class) (x:U),
  x :< truncate A <-> Small A /\ A x.
Proof.
  intros A x. split; intros H1.
  - apply FromClass.Charac in H1. assumption.
  - apply FromClass.Charac. assumption.
Qed.

(* Equivalent classes have equal truncations.                                   *)
Proposition EquivCompat : forall (A B:Class),
  A :~: B -> truncate A = truncate B.
Proof.
  intros A B H1.
  apply FromClass.EquivCompat, Class.Truncate.EquivCompat. assumption.
Qed.

(* If A is small, the class of its truncation is equivalent to A itself.        *)
Proposition WhenSmall : forall (A:Class),
  Small A -> toClass (truncate A) :~: A.
Proof.
  intros A H1. apply Equiv.Tran with (Class.Truncate.truncate A).
  - apply FromClass.ToClass.
  - apply Class.Truncate.WhenSmall. assumption.
Qed.

(* If A is not small, its truncation is the empty set.                          *)
Proposition WhenNotSmall : forall (A:Class),
  ~ Small A -> truncate A = :0:.
Proof.
  intros A H1. apply EqualToClass.
  apply Equiv.Tran with (Class.Truncate.truncate A).
  - apply FromClass.ToClass.
  - apply Equiv.Tran with :0:.
    + apply Class.Truncate.WhenNotSmall. assumption.
    + apply Equiv.Sym, Empty.ToClass.
Qed.

(* If A is equivalent to the empty class, its truncation is the empty set.      *)
Proposition WhenEmpty : forall (A:Class), A :~: :0: -> truncate A = :0:.
Proof.
  intros A H1. apply DoubleInclusion. split; intros x H2.
  - apply Charac in H2. destruct H2 as [_ H2]. apply H1 in H2. contradiction.
  - apply Empty.Charac in H2. contradiction.
Qed.

(* If A is included in B, the class of truncate(A) is also included in B.       *)
Proposition IsIncl : forall (A B:Class),
  A :<=: B -> toClass (truncate A) :<=: B.
Proof.
  intros A B H1 x H2. apply Charac in H2. destruct H2 as [H2 H3].
  apply H1. assumption.
Qed.

