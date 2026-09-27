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

Require Import ZF.Meta.Decl.Class.Relation.Domain.

Import ListNotations.
Open Scope string_scope.

(* Declaration typing.                                                          *)

(* The declaration body for relation domain is well sorted.                     *)
Proposition domain : CheckT (Domain.env) Domain.domain.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Domain.domain. checkT.
Qed.

(* Proposition typing.                                                          *)

(* Compatibility of relation domain with equivalence is well sorted.            *)
Proposition EquivCompat : CheckP (Domain.env) Domain.EquivCompat.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Domain.EquivCompat. checkP.
Qed.

(* Compatibility of relation domain with inclusion is well sorted.              *)
Proposition InclCompat : CheckP (Domain.env) Domain.InclCompat.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Domain.InclCompat. checkP.
Qed.

(* The image-under-first-projection characterization is well sorted.            *)
Proposition ImageUnderFst : CheckP (Domain.env) Domain.ImageUnderFst.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Domain.ImageUnderFst. checkP.
Qed.

(* Smallness of relation domain over a small relation is well sorted.           *)
Proposition IsSmall : CheckP (Domain.env) Domain.IsSmall.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Domain.IsSmall. checkP.
Qed.

(* Domain of an empty relation being empty is well sorted.                      *)
Proposition WhenZero : CheckP (Domain.env) Domain.WhenZero.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Domain.WhenZero. checkP.
Qed.
