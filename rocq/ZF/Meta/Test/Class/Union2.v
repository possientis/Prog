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

Require Import ZF.Meta.Decl.Class.Union2.

Import ListNotations.
Open Scope string_scope.

(* Declaration typing.                                                          *)

(* The declaration body for binary union is well sorted.                        *)
Proposition union2 : CheckT (Union2.env) Union2.union2.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Union2.union2. checkT.
Qed.

(* Proposition typing.                                                          *)

(* Compatibility of binary union with equivalence is well sorted.               *)
Proposition EquivCompat : CheckP (Union2.env) Union2.EquivCompat.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Union2.EquivCompat. checkP.
Qed.

(* Left compatibility of binary union with equivalence is well sorted.          *)
Proposition EquivCompatL : CheckP (Union2.env) Union2.EquivCompatL.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Union2.EquivCompatL. checkP.
Qed.

(* Right compatibility of binary union with equivalence is well sorted.         *)
Proposition EquivCompatR : CheckP (Union2.env) Union2.EquivCompatR.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Union2.EquivCompatR. checkP.
Qed.

(* Smallness of binary union is well sorted.                                    *)
Proposition IsSmall : CheckP (Union2.env) Union2.IsSmall.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Union2.IsSmall. checkP.
Qed.
