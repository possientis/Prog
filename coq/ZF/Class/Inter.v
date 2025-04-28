Require Import ZF.Class.Core.
Require Import ZF.Set.Core.
Require Import ZF.Set.Inter2.
Require Import ZF.Set.Pair.

Require Import ZF.Notation.Inter.
Export ZF.Notation.Inter.

(* The class of sets x which belong to all elements of P.                       *)
Definition inter (P:Class) : Class := fun x =>
  forall y, P y -> x :< y.

(* Notation ":I( P )" := (inter P)                                              *)
Global Instance ClassInter : Inter Class := { inter := inter }.

(* The intersection is compatible with class equivalence.                       *)
Proposition EquivCompat : forall (P Q:Class),
  P :~: Q -> :I(P) :~: :I(Q).
Proof.
  intros P Q H1 x. split; intros H2 y H3; apply H2, H1; assumption.
Qed.

Proposition InterOfPair : forall (a b:U),
  :I(toClass :{a,b}:) :~: toClass (a :/\: b).
Proof.
  intros a b x. split; intros H1.
  - apply Inter2.Charac. split; apply H1.
    + apply Pair.IsInL.
    + apply Pair.IsInR.
  - apply Inter2.Charac in H1. destruct H1 as [H1 H2]. intros y H3.
    apply Pair.Charac in H3. destruct H3 as [H3|H3]; subst; assumption.
Qed.
