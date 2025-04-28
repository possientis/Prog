Require Import ZF.Class.Core.
Require Import ZF.Set.Core.

Require Import ZF.Notation.Inter.
Export ZF.Notation.Inter.

(* The class of all sets x which belongs to all elements of P.                  *)
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
