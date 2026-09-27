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

Require Import ZF.Meta.Decl.Class.Relation.HasValueAt.

Import ListNotations.
Open Scope string_scope.

(* Declaration typing.                                                          *)

(* The declaration body for having a value at a point is well sorted.           *)
Proposition HasValueAt : CheckT (HasValueAt.env) HasValueAt.HasValueAt.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold HasValueAt.HasValueAt. checkT.
Qed.

(* Proposition typing.                                                          *)

(* The intersection characterization of having a value is well sorted.          *)
Proposition AsInter : CheckP (HasValueAt.env) HasValueAt.AsInter.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold HasValueAt.AsInter. checkP.
Qed.

(* The functional-at-point existence characterization is well sorted.           *)
Proposition WhenFunctionalAt :
  CheckP (HasValueAt.env) HasValueAt.WhenFunctionalAt.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold HasValueAt.WhenFunctionalAt. checkP.
Qed.

(* The functional existence characterization is well sorted.                    *)
Proposition WhenFunctional : CheckP (HasValueAt.env) HasValueAt.WhenFunctional.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold HasValueAt.WhenFunctional. checkP.
Qed.
