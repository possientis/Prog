(*Require Import Bool Arith List CpdtTactics. *)
(*Set Implicit Arguments.*)
(*Set Asymetric Patterns.*) (* no impact before Coq version 8.5 *)

Inductive binop : Set := Plus | Times.

Inductive exp : Set :=
| Const : nat -> exp
| Binop : binop -> exp -> exp -> exp.

(*
Definition binopDenote (b : binop) : nat -> nat -> nat :=
  match b with
  | Plus => plus
  | Times => mult
  end.
*)

(*
Definition binopDenote : binop -> nat -> nat -> nat := fun (b : binop) =>
  match b with
  | Plus => plus
  | Times => mult
  end.
*)

Definition binopDenote := fun b =>
  match b with
  | Plus => plus
  | Times => mult
  end.
