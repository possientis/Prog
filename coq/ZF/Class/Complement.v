Require Import ZF.Class.Core.
Require Import ZF.Set.Core.

Require Import ZF.Notation.Not.
Export ZF.Notation.Not.

(* Complement of a class.                                                       *)
Definition complement (A:Class) : Class := fun x => ~ (A x).

(* Notation ":¬: P" := (complement P)                                           *)
Global Instance ClassNot : Not Class := { not := complement }.

Proposition EquivCompat : forall (A B:Class),
  A :~: B -> :¬:A :~: :¬:B.
Proof.
  intros A B H1 x. split; intros H2 H3; apply H2, H1; assumption.
Qed.
