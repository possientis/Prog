Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

Require Import ZF.Meta.Check.Core.
Require Import ZF.Meta.Check.DeclP.
Require Import ZF.Meta.Check.DeclT.
Require Import ZF.Meta.Check.Tactic.
Require Import ZF.Meta.DeclP.
Require Import ZF.Meta.Syntax.
Require Import ZF.Meta.Ty.

Require Import ZF.Meta.Decl.Class.Relation.Functional.

Import ListNotations.
Open Scope string_scope.

(* Declaration typing.                                                          *)

(* The declaration body for being functional is well sorted.                    *)
Proposition Functional : CheckT (Functional.env) Functional.Functional.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Functional.Functional. checkT.
Qed.

(* Proposition typing.                                                          *)

(* Compatibility of functionality with equivalence is well sorted.              *)
Proposition EquivCompat : CheckP (Functional.env) Functional.EquivCompat.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Functional.EquivCompat. checkP.
Qed.

(* Compatibility of functionality with inclusion is well sorted.                *)
Proposition InclCompat : CheckP (Functional.env) Functional.InclCompat.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Functional.InclCompat. checkP.
Qed.

(* Characterization by pointwise functionality is well sorted.                  *)
Proposition IsFunctionalAt : CheckP (Functional.env) Functional.IsFunctionalAt.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Functional.IsFunctionalAt. checkP.
Qed.
