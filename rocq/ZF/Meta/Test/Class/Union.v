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

Require Import ZF.Meta.Decl.Class.Union.

Import ListNotations.
Open Scope string_scope.

(* Declaration typing.                                                          *)

(* The declaration body for class union is well sorted.                         *)
Proposition union : CheckT (Union.env) Union.union.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Union.union. checkT.
Qed.

(* Proposition typing.                                                          *)

(* Compatibility of class union with equivalence is well sorted.                *)
Proposition EquivCompat : CheckP (Union.env) Union.EquivCompat.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Union.EquivCompat. checkP.
Qed.

(* Smallness of class union over a small class is well sorted.                  *)
Proposition IsSmall : CheckP (Union.env) Union.IsSmall.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Union.IsSmall. checkP.
Qed.
