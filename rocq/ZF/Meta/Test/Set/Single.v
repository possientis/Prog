Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

Require Import ZF.Meta.Check.Core.
Require Import ZF.Meta.Check.DeclP.
Require Import ZF.Meta.Check.DeclT.
Require Import ZF.Meta.Check.Tactic.
Require Import ZF.Meta.DeclP.
Require Import ZF.Meta.Syntax.
Require Import ZF.Meta.Ty.

Require Import ZF.Meta.Decl.Set.Single.

Import ListNotations.
Open Scope string_scope.

(* Declaration typing.                                                          *)

(* The singleton declaration is the pair of a set with itself.                  *)
Proposition single : CheckT (Single.env) Single.single.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Single.single. checkT.
Qed.

(* The characterization proposition is well sorted.                             *)
Proposition Charac : CheckP (Single.env) Single.Charac.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Single.Charac. checkP.
Qed.

(* The membership proposition is well sorted.                                   *)
Proposition IsIn : CheckP (Single.env) Single.IsIn.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Single.IsIn. checkP.
Qed.

(* Equality of singletons implies equality of their members.                    *)
Proposition WhenEqual : CheckP (Single.env) Single.WhenEqual.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Single.WhenEqual. checkP.
Qed.

(* The class-inclusion proposition is well sorted.                              *)
Proposition ToClassIncl : CheckP (Single.env) Single.ToClassIncl.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Single.ToClassIncl. checkP.
Qed.

(* The singleton-not-pair proposition is well sorted.                           *)
Proposition IsNotPair : CheckP (Single.env) Single.IsNotPair.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Single.IsNotPair. checkP.
Qed.
