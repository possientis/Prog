Require Import ZF.Class.
Require Import ZF.Core.Not.
Require Import ZF.Set.

(* Complement of a class.                                                       *)
Definition complement (P:Class) : Class := fun x => ~ (P x).

(* Notation ":¬: P" := (complement P)                                           *)
Global Instance ClassNot : Not Class := { not := complement }.

Proposition ComplementCharac : forall (P:Class) (x:U), :¬:P x <-> ~ (P x).
Proof.
  intros P x. split; intros H1; apply H1.
Qed.
