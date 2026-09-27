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

Require Import ZF.Meta.Decl.Class.Diff.

Import ListNotations.
Open Scope string_scope.

(* Declaration typing.                                                          *)

(* The declaration body for class difference is well sorted.                    *)
Proposition diff : CheckT (Diff.env) Diff.diff.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Diff.diff. checkT.
Qed.

(* Proposition typing.                                                          *)

(* Compatibility of class difference with equivalence is well sorted.           *)
Proposition EquivCompat : CheckP (Diff.env) Diff.EquivCompat.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Diff.EquivCompat. checkP.
Qed.

(* Left compatibility of class difference with equivalence is well sorted.      *)
Proposition EquivCompatL : CheckP (Diff.env) Diff.EquivCompatL.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Diff.EquivCompatL. checkP.
Qed.

(* Right compatibility of class difference with equivalence is well sorted.     *)
Proposition EquivCompatR : CheckP (Diff.env) Diff.EquivCompatR.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Diff.EquivCompatR. checkP.
Qed.

(* Compatibility of class difference with inclusion is well sorted.             *)
Proposition InclCompat : CheckP (Diff.env) Diff.InclCompat.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Diff.InclCompat. checkP.
Qed.

(* Left compatibility of class difference with inclusion is well sorted.        *)
Proposition InclCompatL : CheckP (Diff.env) Diff.InclCompatL.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Diff.InclCompatL. checkP.
Qed.

(* Right compatibility of class difference with inclusion is well sorted.       *)
Proposition InclCompatR : CheckP (Diff.env) Diff.InclCompatR.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Diff.InclCompatR. checkP.
Qed.

(* Smallness of class difference over a small class is well sorted.             *)
Proposition IsSmall : CheckP (Diff.env) Diff.IsSmall.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Diff.IsSmall. checkP.
Qed.

(* The zero criterion for class difference is well sorted.                      *)
Proposition WhenZero : CheckP (Diff.env) Diff.WhenZero.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Diff.WhenZero. checkP.
Qed.

(* The nonzero criterion for class difference is well sorted.                   *)
Proposition WhenNotZero : CheckP (Diff.env) Diff.WhenNotZero.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Diff.WhenNotZero. checkP.
Qed.

(* The included-subclass nonzero criterion is well sorted.                      *)
Proposition WhenIncl : CheckP (Diff.env) Diff.WhenIncl.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Diff.WhenIncl. checkP.
Qed.

(* The proper-inclusion nonzero criterion is well sorted.                       *)
Proposition WhenLess : CheckP (Diff.env) Diff.WhenLess.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Diff.WhenLess. checkP.
Qed.

(* Right distribution of difference over union is well sorted.                  *)
Proposition UnionR : CheckP (Diff.env) Diff.UnionR.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Diff.UnionR. checkP.
Qed.

(* Image compatibility of difference under injective classes is well sorted.    *)
Proposition Image : CheckP (Diff.env) Diff.Image.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Diff.Image. checkP.
Qed.

(* Properness of class difference with a set class is well sorted.              *)
Proposition IsProper : CheckP (Diff.env) Diff.IsProper.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Diff.IsProper. checkP.
Qed.

(* Left projection inclusion of class difference is well sorted.                *)
Proposition IsInclL : CheckP (Diff.env) Diff.IsInclL.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Diff.IsInclL. checkP.
Qed.

(* Right projection inclusion of class difference is well sorted.               *)
Proposition IsInclR : CheckP (Diff.env) Diff.IsInclR.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Diff.IsInclR. checkP.
Qed.
