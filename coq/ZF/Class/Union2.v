Require Import ZF.Class.
Require Import ZF.Core.Or.
Require Import ZF.Set.

(* The union of two classes.                                                    *)
Definition union2 (P Q:Class) : Class := fun x => P x \/ Q x.

(* Notation "P :\/: Q" := (union P Q)                                           *)
Global Instance ClassOr : Or Class := { or := union2 }.

Proposition Union2Charac : forall (P Q:Class) (x:U),
  (P :\/: Q) x <-> P x \/ Q x.
Proof.
  intros P Q x. unfold or, ClassOr, union2. split; auto.
Qed.
