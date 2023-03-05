Require Import Logic.Class.Eq.

Require Import Logic.List.In.

Require Import Logic.Lam.Free.
Require Import Logic.Lam.Valid.
Require Import Logic.Lam.Syntax.

(* A map f:v -> v is admissible for a term t if and only if it is valid         *)
(* for t and keeps all its free variables unchanged. An admissible mapping      *)
(* has the property of not altering the alpha-equivalence class of a term       *)
Definition admissible (v:Type) (e:Eq v) (f:v -> v) (t:T v) : Prop :=
  valid f t /\ forall (x:v), x :: Fr t -> f x = x.

Arguments admissible {v} {e}.

