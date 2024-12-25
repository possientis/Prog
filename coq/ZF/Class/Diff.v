Require Import ZF.Class.
Require Import ZF.Class.Complement.
Require Import ZF.Class.Inter.
Require Import ZF.Core.And.
Require Import ZF.Core.Diff.
Require Import ZF.Core.Not.
Require Import ZF.Set.

Definition diff (P Q:Class) : Class := P :/\: :¬:Q.

(* Notation "P :\: Q" := (diff P Q)                                             *)
Global Instance ClassDiff : Diff Class := { diff := diff }.

Proposition DiffCharac : forall (P Q:Class) (x:U),
  (P :\: Q) x <-> P x /\ ~ (Q x).
Proof.
  intros P Q x. split; intros H1; apply H1.
Qed.
