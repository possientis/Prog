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

Require Import ZF.Meta.Decl.Class.InterGen.

Import ListNotations.
Open Scope string_scope.

(* Declaration typing.                                                          *)


(* The declaration body for generalized intersection is well sorted.            *)
Proposition interGen : CheckT (InterGen.env) InterGen.interGen.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold InterGen.interGen. checkT.
Qed.

(* Proposition typing.                                                          *)

(* The forward characterization of generalized intersection is well sorted.     *)
Proposition Charac : CheckP (InterGen.env) InterGen.Charac.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold InterGen.Charac. checkP.
Qed.

(* The reverse characterization of generalized intersection is well sorted.     *)
Proposition CharacRev : CheckP (InterGen.env) InterGen.CharacRev.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold InterGen.CharacRev. checkP.
Qed.

(* Smallness of generalized intersection is well sorted.                        *)
Proposition IsSmall : CheckP (InterGen.env) InterGen.IsSmall.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold InterGen.IsSmall. checkP.
Qed.

(* Generalized intersection over an empty index is well sorted.                 *)
Proposition WhenZero : CheckP (InterGen.env) InterGen.WhenZero.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold InterGen.WhenZero. checkP.
Qed.
