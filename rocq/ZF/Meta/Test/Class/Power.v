Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

Require Import ZF.Meta.Check.CoreT.
Require Import ZF.Meta.Check.CoreP.
Require Import ZF.Meta.Check.DeclP.
Require Import ZF.Meta.Check.DeclT.
Require Import ZF.Meta.Check.Tactic.
Require Import ZF.Meta.DeclP.
Require Import ZF.Meta.DeclT.
Require Import ZF.Meta.SyntaxT.
Require Import ZF.Meta.SyntaxP.
Require Import ZF.Meta.Ty.

Require Import ZF.Meta.Decl.Class.Power.

Import ListNotations.
Open Scope string_scope.

(* Declaration typing.                                                          *)

(* The declaration body for the power class is well sorted.                     *)
Proposition power : CheckT (Power.env) Power.power.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Power.power. checkT.
Qed.

(* Proposition typing.                                                          *)

(* Smallness of the power class is well sorted.                                 *)
Proposition IsSmall : CheckP (Power.env) Power.IsSmall.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Power.IsSmall. checkP.
Qed.
