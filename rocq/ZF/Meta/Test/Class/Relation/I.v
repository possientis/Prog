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

Require Import ZF.Meta.Decl.Class.Relation.I.

Import ListNotations.
Open Scope string_scope.

(* Declaration typing.                                                          *)

(* The identity relation class declaration is well sorted.                      *)
Proposition I : CheckT (I.env) I.I.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold I.I. checkT.
Qed.

(* Proposition typing.                                                          *)

(* The ordered-pair characterization of I is well sorted.                       *)
Proposition Charac2 : CheckP (I.env) I.Charac2.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold I.Charac2. checkP.
Qed.

(* Functionality of I is well sorted.                                           *)
Proposition IsFunctional : CheckP (I.env) I.IsFunctional.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold I.IsFunctional. checkP.
Qed.

(* Relationhood of I is well sorted.                                            *)
Proposition IsRelation : CheckP (I.env) I.IsRelation.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold I.IsRelation. checkP.
Qed.

(* Functionhood of I is well sorted.                                            *)
Proposition IsFunction : CheckP (I.env) I.IsFunction.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold I.IsFunction. checkP.
Qed.

(* Self-converse property of I is well sorted.                                  *)
Proposition Converse : CheckP (I.env) I.Converse.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold I.Converse. checkP.
Qed.

(* One-to-one property of I is well sorted.                                     *)
Proposition IsOneToOne : CheckP (I.env) I.IsOneToOne.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold I.IsOneToOne. checkP.
Qed.

(* Bijection property of I is well sorted.                                      *)
Proposition IsBijection : CheckP (I.env) I.IsBijection.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold I.IsBijection. checkP.
Qed.

(* The domain characterization of I is well sorted.                             *)
Proposition Domain : CheckP (I.env) I.Domain.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold I.Domain. checkP.
Qed.

(* The range characterization of I is well sorted.                              *)
Proposition Range : CheckP (I.env) I.Range.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold I.Range. checkP.
Qed.

(* The FunctionOn property of I over V is well sorted.                          *)
Proposition IsFunctionOn : CheckP (I.env) I.IsFunctionOn.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold I.IsFunctionOn. checkP.
Qed.

(* The BijectionOn property of I over V is well sorted.                         *)
Proposition IsBijectionOn : CheckP (I.env) I.IsBijectionOn.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold I.IsBijectionOn. checkP.
Qed.

(* The Bij property of I from V to V is well sorted.                            *)
Proposition IsBij : CheckP (I.env) I.IsBij.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold I.IsBij. checkP.
Qed.

(* Evaluation of I is well sorted.                                              *)
Proposition Eval : CheckP (I.env) I.Eval.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold I.Eval. checkP.
Qed.

(* The identity isomorphism property is well sorted.                            *)
Proposition IsIsom : CheckP (I.env) I.IsIsom.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold I.IsIsom. checkP.
Qed.

