Require Import bool.
Require Import nat.
Require Import syntax.
Require Import eval.
Require Import state.
Require Import dictionary.
Require Import equiv.

Definition atrans_sound (atrans:aexp -> aexp) : Prop :=
    forall (a:aexp), aequiv a (atrans a).

Definition btrans_sound (btrans:bexp -> bexp) : Prop :=
    forall (b:bexp), bequiv b (btrans b).

Definition ctrans_sound (ctrans:com -> com) : Prop :=
    forall (c:com), cequiv c (ctrans c).


