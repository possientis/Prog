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

Require Import ZF.Meta.Decl.Class.Relation.IsValueAt.

Import ListNotations.
Open Scope string_scope.

(* Declaration typing.                                                          *)

(* The declaration body for being a value at a point is well sorted.            *)
Proposition IsValueAt : CheckT (IsValueAt.env) IsValueAt.IsValueAt.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold IsValueAt.IsValueAt. checkT.
Qed.

(* Proposition typing.                                                          *)

(* Compatibility of being a value at a point with equivalence is well sorted.   *)
Proposition EquivCompat : CheckP (IsValueAt.env) IsValueAt.EquivCompat.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold IsValueAt.EquivCompat. checkP.
Qed.

(* The functional-at-point value characterization is well sorted.               *)
Proposition WhenFunctionalAt :
  CheckP (IsValueAt.env) IsValueAt.WhenFunctionalAt.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold IsValueAt.WhenFunctionalAt. checkP.
Qed.

(* The functional value characterization is well sorted.                        *)
Proposition WhenFunctional : CheckP (IsValueAt.env) IsValueAt.WhenFunctional.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold IsValueAt.WhenFunctional. checkP.
Qed.
