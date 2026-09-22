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

Require Import ZF.Meta.Decl.Set.Specify.

Import ListNotations.
Open Scope string_scope.

(* Declaration typing.                                                          *)

(* The declaration body for set specification is well sorted.                   *)
Proposition specify : CheckT (Specify.env) Specify.specify.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Specify.specify. checkT.
Qed.

(* Proposition typing.                                                          *)

(* The characterization of set specification is well sorted.                    *)
Proposition Charac : CheckP (Specify.env) Specify.Charac.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Specify.Charac. checkP.
Qed.

(* The set-level left inclusion property is well sorted.                        *)
Proposition IsInclL : CheckP (Specify.env) Specify.IsInclL.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Specify.IsInclL. checkP.
Qed.

(* The class-level right inclusion property is well sorted.                     *)
Proposition IsInclR : CheckP (Specify.env) Specify.IsInclR.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Specify.IsInclR. checkP.
Qed.

(* The criterion for a specification to recover its set is well sorted.         *)
Proposition IsA : CheckP (Specify.env) Specify.IsA.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Specify.IsA. checkP.
Qed.
