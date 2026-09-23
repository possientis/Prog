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

Require Import ZF.Meta.Decl.Class.Less.

Import ListNotations.
Open Scope string_scope.

(* Declaration typing.                                                          *)

(* The declaration body for strict class inclusion is well sorted.              *)
Proposition Less : CheckT (Less.env) Less.Less.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Less.Less. checkT.
Qed.

(* Proposition typing.                                                          *)

(* Compatibility of strict inclusion with equivalence is well sorted.           *)
Proposition EquivCompat : CheckP (Less.env) Less.EquivCompat.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Less.EquivCompat. checkP.
Qed.

(* Left compatibility with equivalence is well sorted.                          *)
Proposition EquivCompatL : CheckP (Less.env) Less.EquivCompatL.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Less.EquivCompatL. checkP.
Qed.

(* Right compatibility with equivalence is well sorted.                         *)
Proposition EquivCompatR : CheckP (Less.env) Less.EquivCompatR.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Less.EquivCompatR. checkP.
Qed.

(* The existential characterization of strict inclusion is well sorted.         *)
Proposition Exists : CheckP (Less.env) Less.Exists.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Less.Exists. checkP.
Qed.

(* Inclusion followed by strict inclusion is well sorted.                       *)
Proposition InclLessTran : CheckP (Less.env) Less.InclLessTran.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Less.InclLessTran. checkP.
Qed.

(* Strict inclusion followed by inclusion is well sorted.                       *)
Proposition LessInclTran : CheckP (Less.env) Less.LessInclTran.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Less.LessInclTran. checkP.
Qed.

(* The equivalence-or-strict-inclusion criterion is well sorted.                *)
Proposition EquivOrLess : CheckP (Less.env) Less.EquivOrLess.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Less.EquivOrLess. checkP.
Qed.
