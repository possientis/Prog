Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

Require Import ZF.Meta.Check.CoreP.
Require Import ZF.Meta.Check.DeclP.
Require Import ZF.Meta.Check.Tactic.
Require Import ZF.Meta.DeclP.
Require Import ZF.Meta.SyntaxT.
Require Import ZF.Meta.SyntaxP.
Require Import ZF.Meta.Ty.

Require Import ZF.Meta.Decl.Class.Relation.IA.

Import ListNotations.
Open Scope string_scope.

(* Proposition typing.                                                          *)

(* The element characterization of restricted identity is well sorted.          *)
Proposition Charac : CheckP (IA.env) IA.Charac.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold IA.Charac. checkP.
Qed.

(* The ordered-pair characterization of restricted identity is well sorted.     *)
Proposition Charac2 : CheckP (IA.env) IA.Charac2.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold IA.Charac2. checkP.
Qed.

(* Functionality of restricted identity is well sorted.                         *)
Proposition IsFunctional : CheckP (IA.env) IA.IsFunctional.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold IA.IsFunctional. checkP.
Qed.

(* Relationhood of restricted identity is well sorted.                          *)
Proposition IsRelation : CheckP (IA.env) IA.IsRelation.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold IA.IsRelation. checkP.
Qed.

(* Functionhood of restricted identity is well sorted.                          *)
Proposition IsFunction : CheckP (IA.env) IA.IsFunction.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold IA.IsFunction. checkP.
Qed.

(* The self-converse property of restricted identity is well sorted.            *)
Proposition Converse : CheckP (IA.env) IA.Converse.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold IA.Converse. checkP.
Qed.

(* The one-to-one property of restricted identity is well sorted.               *)
Proposition IsOneToOne : CheckP (IA.env) IA.IsOneToOne.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold IA.IsOneToOne. checkP.
Qed.

(* The bijection property of restricted identity is well sorted.                *)
Proposition IsBijection : CheckP (IA.env) IA.IsBijection.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold IA.IsBijection. checkP.
Qed.

(* The domain characterization of restricted identity is well sorted.           *)
Proposition Domain : CheckP (IA.env) IA.Domain.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold IA.Domain. checkP.
Qed.

(* The range characterization of restricted identity is well sorted.            *)
Proposition Range : CheckP (IA.env) IA.Range.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold IA.Range. checkP.
Qed.

(* The FunctionOn property of restricted identity is well sorted.               *)
Proposition IsFunctionOn : CheckP (IA.env) IA.IsFunctionOn.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold IA.IsFunctionOn. checkP.
Qed.

(* The BijectionOn property of restricted identity is well sorted.              *)
Proposition IsBijectionOn : CheckP (IA.env) IA.IsBijectionOn.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold IA.IsBijectionOn. checkP.
Qed.

(* The Bij property of restricted identity is well sorted.                      *)
Proposition IsBij : CheckP (IA.env) IA.IsBij.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold IA.IsBij. checkP.
Qed.

(* Evaluation of restricted identity is well sorted.                            *)
Proposition Eval : CheckP (IA.env) IA.Eval.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold IA.Eval. checkP.
Qed.

(* Uniqueness of restricted identity among fixed functions is well sorted.      *)
Proposition Equal : CheckP (IA.env) IA.Equal.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold IA.Equal. checkP.
Qed.

(* The restricted identity isomorphism property is well sorted.                 *)
Proposition IsIsom : CheckP (IA.env) IA.IsIsom.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold IA.IsIsom. checkP.
Qed.

(* The inverse-after-function identity law is well sorted.                      *)
Proposition IsConverseFF : CheckP (IA.env) IA.IsConverseFF.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold IA.IsConverseFF. checkP.
Qed.

(* The function-after-inverse identity law is well sorted.                      *)
Proposition IsFConverseF : CheckP (IA.env) IA.IsFConverseF.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold IA.IsFConverseF. checkP.
Qed.

(* The left identity law for composition is well sorted.                        *)
Proposition IdentityL : CheckP (IA.env) IA.IdentityL.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold IA.IdentityL. checkP.
Qed.

(* The right identity law for composition is well sorted.                       *)
Proposition IdentityR : CheckP (IA.env) IA.IdentityR.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold IA.IdentityR. checkP.
Qed.

(* The inverse-left composite cancellation law is well sorted.                  *)
Proposition WhenIsConverseGF : CheckP (IA.env) IA.WhenIsConverseGF.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold IA.WhenIsConverseGF. checkP.
Qed.

(* The right-inverse composite cancellation law is well sorted.                 *)
Proposition WhenIsGConverseF : CheckP (IA.env) IA.WhenIsGConverseF.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold IA.WhenIsGConverseF. checkP.
Qed.

