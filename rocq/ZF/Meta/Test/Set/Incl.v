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

Require Import ZF.Meta.Decl.Set.Incl.

Import ListNotations.
Open Scope string_scope.

(* Declaration typing.                                                          *)

(* The declaration body for set inclusion is well sorted.                       *)
Proposition Incl : CheckT (Incl.env) Incl.Incl.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Incl.Incl. checkT.
Qed.

(* Proposition typing.                                                          *)

(* Lifting set inclusion to class inclusion is well sorted.                     *)
Proposition ToClass : CheckP (Incl.env) Incl.ToClass.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Incl.ToClass. checkP.
Qed.

(* Reflecting class inclusion back to set inclusion is well sorted.             *)
Proposition FromClass : CheckP (Incl.env) Incl.FromClass.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Incl.FromClass. checkP.
Qed.

(* Double set inclusion characterizes equality and is well sorted.              *)
Proposition Double : CheckP (Incl.env) Incl.Double.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Incl.Double. checkP.
Qed.

(* Reflexivity of set inclusion is well sorted.                                 *)
Proposition Refl : CheckP (Incl.env) Incl.Refl.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Incl.Refl. checkP.
Qed.

(* Antisymmetry of set inclusion is well sorted.                                *)
Proposition Anti : CheckP (Incl.env) Incl.Anti.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Incl.Anti. checkP.
Qed.

(* Transitivity of set inclusion is well sorted.                                *)
Proposition Tran : CheckP (Incl.env) Incl.Tran.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Incl.Tran. checkP.
Qed.
