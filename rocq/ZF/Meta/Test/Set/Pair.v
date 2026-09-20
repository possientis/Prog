Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

Require Import ZF.Meta.Check.Core.
Require Import ZF.Meta.Check.DeclP.
Require Import ZF.Meta.Check.DeclT.
Require Import ZF.Meta.Check.Tactic.
Require Import ZF.Meta.DeclP.
Require Import ZF.Meta.SyntaxT.
Require Import ZF.Meta.SyntaxP.
Require Import ZF.Meta.Ty.

Require Import ZF.Meta.Decl.Set.Pair.

Import ListNotations.
Open Scope string_scope.

(* Declaration typing.                                                          *)

(* The declaration body for IsPairOf recognizes the two selected sets.          *)
Proposition IsPairOf : CheckT (Pair.env) Pair.IsPairOf.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Pair.IsPairOf. checkT.
Qed.

(* The existence proof declaration is well sorted.                              *)
Proposition Exists : CheckP (Pair.env) Pair.Exists.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Pair.Exists. checkP.
Qed.

(* The uniqueness proof declaration is well sorted.                             *)
Proposition Unique : CheckP (Pair.env) Pair.Unique.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Pair.Unique. checkP.
Qed.

(* The declaration body for pair denotes a set backed by proof references.      *)
Proposition pair : CheckT (Pair.env) Pair.pair.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Pair.pair. checkT.
Qed.

(* The characterization proposition is well sorted.                             *)
Proposition Charac : CheckP (Pair.env) Pair.Charac.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Pair.Charac. checkP.
Qed.

(* The left membership proposition is well sorted.                              *)
Proposition IsInL : CheckP (Pair.env) Pair.IsInL.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Pair.IsInL. checkP.
Qed.

(* The right membership proposition is well sorted.                             *)
Proposition IsInR : CheckP (Pair.env) Pair.IsInR.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Pair.IsInR. checkP.
Qed.

(* The class-inclusion proposition is well sorted.                              *)
Proposition ToClassIncl : CheckP (Pair.env) Pair.ToClassIncl.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Pair.ToClassIncl. checkP.
Qed.
