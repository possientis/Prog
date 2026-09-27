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

Require Import ZF.Meta.Decl.Class.Relation.Snd.

Import ListNotations.
Open Scope string_scope.

(* Declaration typing.                                                          *)

(* The declaration body for second projection is well sorted.                   *)
Proposition Snd : CheckT (Snd.env) Snd.Snd.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Snd.Snd. checkT.
Qed.

(* Proposition typing.                                                          *)

(* The binary characterization of second projection is well sorted.             *)
Proposition Charac2 : CheckP (Snd.env) Snd.Charac2.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Snd.Charac2. checkP.
Qed.

(* Functionality of second projection is well sorted.                           *)
Proposition IsFunctional : CheckP (Snd.env) Snd.IsFunctional.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Snd.IsFunctional. checkP.
Qed.
