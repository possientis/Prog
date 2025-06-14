Require Import ZF.Axiom.Classic.
Require Import ZF.Class.Core.
Require Import ZF.Class.Empty.
Require Import ZF.Class.Small.
Require Import ZF.Set.Core.

(* The truncate function reduces a class to the empty class if not small.       *)
Definition truncate (A:Class) : Class := fun x =>
  Small A /\ A x.

Proposition WhenSmall : forall (A:Class),
  Small A -> truncate A :~: A.
Proof.
  intros A H1 x. split; intros H2.
  - apply H2.
  - split; assumption.
Qed.

Proposition WhenNotSmall : forall (A:Class),
  ~ Small A -> truncate A :~: :0:.
Proof.
  intros A H1 x. split; intros H2.
  - apply H1, H2.
  - contradiction.
Qed.

(* The truncated class is always small.                                         *)
Proposition IsSmall : forall (A:Class), Small (truncate A).
Proof.
  intros A.
  assert (Small A \/ ~ Small A) as H1. { apply LawExcludedMiddle. }
  destruct H1 as [H1|H1].
  - apply Small.EquivCompat with A. 2: assumption.
    apply EquivSym, WhenSmall. assumption.
  - apply Small.EquivCompat with :0:.
    + apply EquivSym, WhenNotSmall. assumption.
    + apply Empty.IsSmall.
Qed.

