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

Require Import ZF.Meta.Decl.Class.Proper.

Import ListNotations.
Open Scope string_scope.

(* Declaration typing.                                                          *)

(* The declaration body for proper classes is well sorted.                      *)
Proposition Proper : CheckT (Proper.env) Proper.Proper.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Proper.Proper. checkT.
Qed.

(* Proposition typing.                                                          *)

(* A proper class being non-empty is well sorted.                               *)
Proposition IsNotEmpty : CheckP (Proper.env) Proper.IsNotEmpty.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Proper.IsNotEmpty. checkP.
Qed.
