Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

Require Import ZF.Meta.Check.Core.
Require Import ZF.Meta.Check.DeclT.
Require Import ZF.Meta.Check.Tactic.
Require Import ZF.Meta.Syntax.
Require Import ZF.Meta.Ty.

Require Import ZF.Meta.Decl.Axiom.Define.

Import ListNotations.
Open Scope string_scope.

(* Declaration typing.                                                          *)

(* The declaration body for inhabitation of a class is well sorted.             *)
Proposition Exists : CheckT (Define.env) Define.Exists.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Define.Exists. checkT.
Qed.

(* The declaration body for uniqueness of a class element is well sorted.       *)
Proposition Unique : CheckT (Define.env) Define.Unique.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Define.Unique. checkT.
Qed.
