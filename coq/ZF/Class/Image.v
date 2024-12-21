Declare Scope ZF_Class_Image_scope.
Open Scope    ZF_Class_Image_scope.

Require Import ZF.Class.
Require Import ZF.Class.Include.
Require Import ZF.Core.Image.
Require Import ZF.Core.Leq.
Require Import ZF.Set.
Require Import ZF.Set.OrdPair.


(* Direct image of a class Q by a class P.                                      *)
Definition image (P Q:Class) : Class := fun y =>
  exists x, Q x /\ P :(x,y):.

(* Notation "P :[ Q ]:" := (image P Q)                                          *)
Global Instance ClassImage : Image Class Class := { image := image }.

Proposition ImageMonotone : forall (P Q R S:Class),
  P :<=: Q -> R :<=: S -> P:[R]: :<=: Q:[S]:.
Proof.
  intros P Q R S H1 H2 y H3. unfold image in H3. destruct H3 as [x [H3 H4]].
  unfold image. exists x. split.
  - apply H2. assumption.
  - apply H1. assumption.
Qed.
