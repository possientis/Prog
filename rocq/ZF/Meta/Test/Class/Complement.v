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

Require Import ZF.Meta.Decl.Class.Complement.

Import ListNotations.
Open Scope string_scope.

(* Declaration typing.                                                          *)

(* The declaration body for class complementation is well sorted.               *)
Proposition complement : CheckT (Complement.env) Complement.complement.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Complement.complement. checkT.
Qed.

(* Proposition typing.                                                          *)

(* Compatibility of complementation with equivalence is well sorted.            *)
Proposition EquivCompat : CheckP (Complement.env) Complement.EquivCompat.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Complement.EquivCompat. checkP.
Qed.

(* Reverse compatibility of complementation with inclusion is well sorted.      *)
Proposition InclCompat : CheckP (Complement.env) Complement.InclCompat.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Complement.InclCompat. checkP.
Qed.
