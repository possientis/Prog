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

Require Import ZF.Meta.Decl.Class.Relation.Cmp.

Import ListNotations.
Open Scope string_scope.

(* Declaration typing.                                                          *)


(* The declaration body for composition comparison is well sorted.              *)
Proposition Cmp : CheckT (Cmp.env) Cmp.Cmp.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Cmp.Cmp. checkT.
Qed.

(* Proposition typing.                                                          *)

(* The binary characterization of composition comparison is well sorted.        *)
Proposition Charac2 : CheckP (Cmp.env) Cmp.Charac2.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Cmp.Charac2. checkP.
Qed.

(* Functionality of composition comparison is well sorted.                      *)
Proposition IsFunctional : CheckP (Cmp.env) Cmp.IsFunctional.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Cmp.IsFunctional. checkP.
Qed.
