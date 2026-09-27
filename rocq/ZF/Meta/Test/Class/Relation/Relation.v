Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

Require Import ZF.Meta.Check.CoreT.
Require Import ZF.Meta.Check.CoreP.
Require Import ZF.Meta.Check.DeclP.
Require Import ZF.Meta.Check.DeclT.
Require Import ZF.Meta.Check.Tactic.
Require Import ZF.Meta.DeclP.
Require Import ZF.Meta.SyntaxT.
Require Import ZF.Meta.SyntaxP.
Require Import ZF.Meta.Ty.

Require Import ZF.Meta.Decl.Class.Relation.Relation.

Import ListNotations.
Open Scope string_scope.

(* Declaration typing.                                                          *)

(* The declaration body for being a relation is well sorted.                    *)
Proposition Relation : CheckT (Relation.env) Relation.Relation.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Relation.Relation. checkT.
Qed.

(* Proposition typing.                                                          *)

(* Compatibility of relationhood with equivalence is well sorted.               *)
Proposition EquivCompat : CheckP (Relation.env) Relation.EquivCompat.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Relation.EquivCompat. checkP.
Qed.

(* The union of relation classes is well sorted.                                *)
Proposition Union2 : CheckP (Relation.env) Relation.Union2.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Relation.Union2. checkP.
Qed.

(* Smallness of functional relations with small domains is well sorted.         *)
Proposition IsSmall : CheckP (Relation.env) Relation.IsSmall.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Relation.IsSmall. checkP.
Qed.
