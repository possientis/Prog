Require Import Logic.Class.Eq.

Require Import Logic.List.In.

Require Import Logic.Fol.Free.
Require Import Logic.Fol.Valid.
Require Import Logic.Fol.Syntax.

Definition admissible (v:Type) (e:Eq v) (f:v -> v) (p:P v) : Prop :=
  valid f p /\ forall (x:v), x :: Fr p -> f x = x.

Arguments admissible {v} {e}.
