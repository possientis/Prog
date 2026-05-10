Require Import ZF.Class.Diff.
Require Import ZF.Class.Equiv.
Require Import ZF.Class.Incl.
Require Import ZF.Class.Proper.
Require Import ZF.Class.Small.
Require Import ZF.Set.Core.

Export ZF.Notation.Diff.

Definition diff (A:Class) (a:U) : Class := A :\: toClass a.

(* Notation "A :\: a" := (diff A a)                                             *)
Global Instance ClassDiffBySet : Diff Class U := { diff := diff }.

(* An element is in A minus a iff it is in A and not a member of a.             *)
Proposition Charac : forall (A:Class) (a:U) (x:U),
  (A :\: a) x <-> A x /\ ~ x :< a.
Proof.
  (* Proof by Claude.                                                           *)
  intros A a x. unfold diff. split; intros H1.
  - destruct H1 as [H1 H2]. split. 1: assumption.
    intros H3. apply H2. apply H3.
  - destruct H1 as [H1 H2]. split. 1: assumption.
    intros H3. apply H2. apply H3.
Qed.

(* The class-by-set difference is included in the original class.               *)
Proposition IsInclL : forall (A:Class) (a:U),
  A :\: a :<=: A.
Proof.
  (* Proof by Claude.                                                           *)
  intros A a. apply Class.Diff.IsInclL.
Qed.

(* The class-by-set difference of a small class is small.                       *)
Proposition IsSmall : forall (A:Class) (a:U),
  Small A -> Small (A :\: a).
Proof.
  (* Proof by Claude.                                                           *)
  intros A a H1. apply Class.Diff.IsSmall. assumption.
Qed.

(* The class-by-set difference of a proper class is proper.                     *)
Proposition IsProper : forall (A:Class) (a:U),
  Proper A -> Proper (A :\: a).
Proof.
  (* Proof by Claude.                                                           *)
  intros A a H1. apply Class.Diff.MinusASet. assumption.
Qed.

