Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

Require Import ZF.Meta.Check.Core.
Require Import ZF.Meta.Check.DeclP.
Require Import ZF.Meta.Check.DeclT.
Require Import ZF.Meta.Check.Tactic.
Require Import ZF.Meta.DeclP.
Require Import ZF.Meta.SyntaxT.
Require Import ZF.Meta.SyntaxP.
Require Import ZF.Meta.Ty.

Require Import ZF.Meta.Decl.Class.IsSetOf.

Import ListNotations.
Open Scope string_scope.

(* Declaration typing.                                                          *)

(* The declaration body for sets defined by a class is well sorted.             *)
Proposition IsSetOf : CheckT (IsSetOf.env) IsSetOf.IsSetOf.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold IsSetOf.IsSetOf. checkT.
Qed.

(* Proposition typing.                                                          *)

(* Existence of a set defined by a small class is well sorted.                  *)
Proposition Exists : CheckP (IsSetOf.env) IsSetOf.Exists.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold IsSetOf.Exists. checkP.
Qed.

(* Uniqueness of a set defined by a class is well sorted.                       *)
Proposition Unique : CheckP (IsSetOf.env) IsSetOf.Unique.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold IsSetOf.Unique. checkP.
Qed.

(* Compatibility of sets defined by classes with equivalence is well sorted.    *)
Proposition EquivCompat : CheckP (IsSetOf.env) IsSetOf.EquivCompat.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold IsSetOf.EquivCompat. checkP.
Qed.

(* The class of members of a defined set is well sorted.                        *)
Proposition ToClass : CheckP (IsSetOf.env) IsSetOf.ToClass.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold IsSetOf.ToClass. checkP.
Qed.
