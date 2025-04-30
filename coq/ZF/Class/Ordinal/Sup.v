Require Import ZF.Class.Core.
Require Import ZF.Class.Ordinal.Core.
Require Import ZF.Class.Union.
Require Import ZF.Class.Inter2.
Require Import ZF.Set.Core.

Require Import ZF.Notation.SupBelow.
Export ZF.Notation.SupBelow.

(* The supremum of the class A.                                                 *)
Definition sup (A:Class) : Class := :U(A :/\: On).

(* The supremum of the class A below a.                                         *)
Definition supBelow (b:U)(A:Class) : Class := :U(A :/\: On :/\: toClass b).

(* Notation "sup(:< b ) A" := (supBelow b A)                                    *)
Global Instance ClassSupBelow : SupBelow Class := { supBelow := supBelow }.

Proposition EquivCompat : forall (A B:Class),
  A :~: B -> sup A :~: sup B.
Proof.
  intros A B H1. apply Union.EquivCompat, Inter2.EquivCompatL. assumption.
Qed.
