Require Import ZF.Class.
Require Import ZF.Core.Or.
Require Import ZF.Core.Union.
Require Import ZF.Set.

(* The union class of a class.                                                  *)
Definition union (P:Class) : Class := fun x =>
  exists y, x :< y /\ P y.

(* Notation ":U( P )" := (union P)                                              *)
Global Instance ClassUnion : Union Class := { union := union }.

(* The union of two classes.                                                    *)
Definition union2 (P Q:Class) : Class := fun x => P x \/ Q x.

(* Notation "P :\/: Q" := (union P Q)                                           *)
Global Instance ClassOr : Or Class := { or := union2 }.

Proposition Union2Charac : forall (P Q:Class) (x:U),
  (P :\/: Q) x <-> P x \/ Q x.
Proof.
  intros P Q x. unfold or, ClassOr, union. split; auto.
Qed.
