Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

Require Import ZF.Meta.Check.CoreT.
Require Import ZF.Meta.Check.CoreP.
Require Import ZF.Meta.Check.DeclP.
Require Import ZF.Meta.Check.DeclT.
Require Import ZF.Meta.Check.Tactic.
Require Import ZF.Meta.DeclP.
Require Import ZF.Meta.SyntaxT.
Require Import ZF.Meta.SyntaxP.
Require Import ZF.Meta.Ty.

Require Import ZF.Meta.Decl.Class.Incl.

Import ListNotations.
Open Scope string_scope.

(* Declaration typing.                                                          *)

(* The declaration body for inclusion compares two classes pointwise.           *)
Proposition Incl : CheckT (Incl.env) Incl.Incl.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Incl.Incl. checkT.
Qed.

(* Proposition typing.                                                          *)

(* Double inclusion and equivalence form a well-sorted proposition.             *)
Proposition Double : CheckP (Incl.env) Incl.Double.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Incl.Double. checkP.
Qed.

(* Compatibility of inclusion with equivalence is well sorted.                  *)
Proposition EquivCompat : CheckP (Incl.env) Incl.EquivCompat.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Incl.EquivCompat. checkP.
Qed.

(* Left compatibility of inclusion with equivalence is well sorted.             *)
Proposition EquivCompatL : CheckP (Incl.env) Incl.EquivCompatL.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Incl.EquivCompatL. checkP.
Qed.

(* Right compatibility of inclusion with equivalence is well sorted.            *)
Proposition EquivCompatR : CheckP (Incl.env) Incl.EquivCompatR.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Incl.EquivCompatR. checkP.
Qed.

(* Reflexivity of inclusion is a well-sorted proposition.                       *)
Proposition Refl : CheckP (Incl.env) Incl.Refl.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Incl.Refl. checkP.
Qed.

(* Antisymmetry of inclusion is a well-sorted proposition.                      *)
Proposition Anti : CheckP (Incl.env) Incl.Anti.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Incl.Anti. checkP.
Qed.

(* Transitivity of inclusion is a well-sorted proposition.                      *)
Proposition Tran : CheckP (Incl.env) Incl.Tran.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Incl.Tran. checkP.
Qed.
