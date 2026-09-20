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

Require Import ZF.Meta.Decl.Class.Relation.FunctionalAt.

Import ListNotations.
Open Scope string_scope.

(* Declaration typing.                                                          *)

(* The declaration body for being functional at a point is well sorted.         *)
Proposition FunctionalAt : CheckT (FunctionalAt.env) FunctionalAt.FunctionalAt.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold FunctionalAt.FunctionalAt. checkT.
Qed.

(* Proposition typing.                                                          *)

(* Compatibility of being functional at a point is well sorted.                 *)
Proposition EquivCompat : CheckP (FunctionalAt.env) FunctionalAt.EquivCompat.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold FunctionalAt.EquivCompat. checkP.
Qed.

(* The negation characterization is well sorted.                                *)
Proposition WhenNot : CheckP (FunctionalAt.env) FunctionalAt.WhenNot.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold FunctionalAt.WhenNot. checkP.
Qed.
