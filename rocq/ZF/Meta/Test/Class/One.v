Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

Require Import ZF.Meta.Check.CoreT.
Require Import ZF.Meta.Check.DeclT.
Require Import ZF.Meta.Check.Tactic.
Require Import ZF.Meta.DeclT.
Require Import ZF.Meta.SyntaxT.
Require Import ZF.Meta.Ty.

Require Import ZF.Meta.Decl.Class.One.

Import ListNotations.
Open Scope string_scope.

(* Declaration typing.                                                          *)

(* The declaration body for the singleton-empty class is well sorted.           *)
Proposition one : CheckT (One.env) One.one.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold One.one. checkT.
Qed.
