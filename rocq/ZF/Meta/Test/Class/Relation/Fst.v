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

Require Import ZF.Meta.Decl.Class.Relation.Fst.

Import ListNotations.
Open Scope string_scope.

(* Declaration typing.                                                          *)

(* The declaration body for first projection is well sorted.                    *)
Proposition Fst : CheckT (Fst.env) Fst.Fst.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Fst.Fst. checkT.
Qed.

(* Proposition typing.                                                          *)

(* The binary characterization of first projection is well sorted.              *)
Proposition Charac2 : CheckP (Fst.env) Fst.Charac2.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Fst.Charac2. checkP.
Qed.

(* Functionality of first projection is well sorted.                            *)
Proposition IsFunctional : CheckP (Fst.env) Fst.IsFunctional.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Fst.IsFunctional. checkP.
Qed.
