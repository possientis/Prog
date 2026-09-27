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

Require Import ZF.Meta.Decl.Class.Relation.Switch.

Import ListNotations.
Open Scope string_scope.

(* Declaration typing.                                                          *)

(* The declaration body for switching ordered pairs is well sorted.             *)
Proposition Switch : CheckT (Switch.env) Switch.Switch.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Switch.Switch. checkT.
Qed.

(* Proposition typing.                                                          *)

(* The binary characterization of switching ordered pairs is well sorted.       *)
Proposition Charac2 : CheckP (Switch.env) Switch.Charac2.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Switch.Charac2. checkP.
Qed.

(* Functionality of switching ordered pairs is well sorted.                     *)
Proposition IsFunctional : CheckP (Switch.env) Switch.IsFunctional.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Switch.IsFunctional. checkP.
Qed.
