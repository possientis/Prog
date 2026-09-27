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

Require Import ZF.Meta.Decl.Class.Truncate.

Import ListNotations.
Open Scope string_scope.

(* Declaration typing.                                                          *)

(* The declaration body for class truncation is well sorted.                    *)
Proposition truncate : CheckT (Truncate.env) Truncate.truncate.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Truncate.truncate. checkT.
Qed.

(* Proposition typing.                                                          *)

(* Compatibility of truncation with equivalence is well sorted.                 *)
Proposition EquivCompat : CheckP (Truncate.env) Truncate.EquivCompat.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Truncate.EquivCompat. checkP.
Qed.

(* The small-class truncation criterion is well sorted.                         *)
Proposition WhenSmall : CheckP (Truncate.env) Truncate.WhenSmall.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Truncate.WhenSmall. checkP.
Qed.

(* The non-small-class truncation criterion is well sorted.                     *)
Proposition WhenNotSmall : CheckP (Truncate.env) Truncate.WhenNotSmall.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Truncate.WhenNotSmall. checkP.
Qed.

(* Smallness of truncated classes is well sorted.                               *)
Proposition IsSmall : CheckP (Truncate.env) Truncate.IsSmall.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Truncate.IsSmall. checkP.
Qed.
