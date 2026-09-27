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

Require Import ZF.Meta.Decl.Class.Singleton.

Import ListNotations.
Open Scope string_scope.

(* Declaration typing.                                                          *)

(* The declaration body for the class of singletons is well sorted.             *)
Proposition Singleton : CheckT (Singleton.env) Singleton.Singleton.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Singleton.Singleton. checkT.
Qed.

(* Proposition typing.                                                          *)

(* Properness of the class of singletons is well sorted.                        *)
Proposition IsProper : CheckP (Singleton.env) Singleton.IsProper.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Singleton.IsProper. checkP.
Qed.
