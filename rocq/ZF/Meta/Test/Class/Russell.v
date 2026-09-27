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

Require Import ZF.Meta.Decl.Class.Russell.

Import ListNotations.
Open Scope string_scope.

(* Declaration typing.                                                          *)

(* The declaration body for Russell's class is well sorted.                     *)
Proposition Ru : CheckT (Russell.env) Russell.Ru.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Russell.Ru. checkT.
Qed.

(* Proposition typing.                                                          *)

(* Properness of Russell's class is well sorted.                                *)
Proposition ProperRu : CheckP (Russell.env) Russell.ProperRu.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Russell.ProperRu. checkP.
Qed.

(* Non-existence of a universal set is well sorted.                             *)
Proposition Russell : CheckP (Russell.env) Russell.Russell.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Russell.Russell. checkP.
Qed.
