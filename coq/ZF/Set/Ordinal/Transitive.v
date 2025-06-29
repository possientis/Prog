Require Import ZF.Class.Equiv.
Require Import ZF.Class.Incl.
Require Import ZF.Class.Ordinal.Transitive.
Require Import ZF.Set.Core.

(* A set is said to be transitive if it is a transitive class.                  *)
Definition Transitive (a:U) : Prop
  := Class.Ordinal.Transitive.Transitive (toClass a).

Proposition Charac : forall (a:U),
  Transitive a <-> forall x y, x :< y ->  y :< a -> x :< a.
Proof.
  intros a. split; intros H1.
  - intros x y H2 H3. specialize (H1 y H3). apply H1. assumption.
  - intros y H2 x H3. apply H1 with y; assumption.
Qed.
