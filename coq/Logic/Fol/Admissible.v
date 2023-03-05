Require Import Logic.Class.Eq.

Require Import Logic.List.In.

Require Import Logic.Fol.Free.
Require Import Logic.Fol.Valid.
Require Import Logic.Fol.Syntax.

(* A map f:v -> v is admissible for a formula p if and only if it is valid      *)
(* for p and keeps all its free variables unchanged. An admissible mapping      *)
(* has the property of not altering the alpha-equivalence class of a formula    *)
Definition admissible (v:Type) (e:Eq v) (f:v -> v) (p:P v) : Prop :=
  valid f p /\ forall (x:v), x :: Fr p -> f x = x.

Arguments admissible {v} {e}.
