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

Require Import ZF.Meta.Decl.Set.Power.

Import ListNotations.
Open Scope string_scope.

(* Declaration typing.                                                          *)

(* The declaration body for the power set is well sorted.                       *)
Proposition power : CheckT (Power.env) Power.power.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Power.power. checkT.
Qed.

(* Proposition typing.                                                          *)

(* The characterization of the power set is well sorted.                        *)
Proposition Charac : CheckP (Power.env) Power.Charac.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Power.Charac. checkP.
Qed.

(* Every set belonging to its own power set is well sorted.                     *)
Proposition IsIn : CheckP (Power.env) Power.IsIn.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Power.IsIn. checkP.
Qed.

(* The power set of the empty set being the empty singleton is well sorted.     *)
Proposition WhenZero : CheckP (Power.env) Power.WhenZero.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Power.WhenZero. checkP.
Qed.
