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

Require Import ZF.Meta.Decl.Class.Order.Transport.

Import ListNotations.
Open Scope string_scope.

(* Declaration typing.                                                          *)

(* The transported relation class declaration is well sorted.                   *)
Proposition transport : CheckT (Transport.env) Transport.transport.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Transport.transport. checkT.
Qed.

(* Proposition typing.                                                          *)

(* The characterization of transported evaluated pairs is well sorted.          *)
Proposition Charac2F : CheckP (Transport.env) Transport.Charac2F.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Transport.Charac2F. checkP.
Qed.

(* The product inclusion for transported relations is well sorted.              *)
Proposition IsIncl : CheckP (Transport.env) Transport.IsIncl.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Transport.IsIncl. checkP.
Qed.

(* Smallness of transported relations is well sorted.                           *)
Proposition IsSmall : CheckP (Transport.env) Transport.IsSmall.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Transport.IsSmall. checkP.
Qed.

