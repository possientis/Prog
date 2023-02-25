Require Import Logic.Class.Eq.

Require Import Logic.List.In.

Require Import Logic.Lam.Free.
Require Import Logic.Lam.Valid.
Require Import Logic.Lam.Syntax.

Definition admissible (v:Type) (e:Eq v) (f:v -> v) (t:T v) : Prop :=
  valid f t /\ forall (x:v), x :: Fr t -> f x = x.

Arguments admissible {v} {e}.

