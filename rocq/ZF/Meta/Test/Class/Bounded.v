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

Require Import ZF.Meta.Decl.Class.Bounded.

Import ListNotations.
Open Scope string_scope.

(* Declaration typing.                                                          *)

(* The declaration body for bounded classes is well sorted.                     *)
Proposition Bounded : CheckT (Bounded.env) Bounded.Bounded.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Bounded.Bounded. checkT.
Qed.

(* Proposition typing.                                                          *)

(* The equivalence of boundedness and smallness is well sorted.                 *)
Proposition IsSmall : CheckP (Bounded.env) Bounded.IsSmall.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Bounded.IsSmall. checkP.
Qed.
