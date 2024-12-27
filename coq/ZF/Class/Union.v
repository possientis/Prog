Declare Scope ZF_Class_Union_scope.
Open    Scope ZF_Class_Union_scope.

Require Import ZF.Class.
Require Import ZF.Core.Or.
Require Import ZF.Set.

(* The union class of a class.                                                  *)
Definition union (P:Class) : Class := fun x =>
  exists y, x :< y /\ P y.

Notation ":U( P )" := (union P)
  (at level 0, no associativity) : ZF_Class_Union_scope.

(* The union of two classes.                                                    *)
Definition union2 (P Q:Class) : Class := fun x => P x \/ Q x.

(* Notation "P :\/: P" := (union P Q)                                           *)
Global Instance ClassOr : Or Class := { or := union2 }.

Proposition UnionCharac : forall (P Q:Class) (x:U),
  (P :\/: Q) x <-> P x \/ Q x.
Proof.
  intros P Q x. unfold or, ClassOr, union. split; auto.
Qed.
