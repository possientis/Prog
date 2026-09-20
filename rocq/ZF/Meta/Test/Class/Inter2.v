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

Require Import ZF.Meta.Decl.Class.Inter2.

Import ListNotations.
Open Scope string_scope.

(* Declaration typing.                                                          *)

(* The declaration body for binary intersection is well sorted.                 *)
Proposition inter2 : CheckT (Inter2.env) Inter2.inter2.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Inter2.inter2. checkT.
Qed.

(* Proposition typing.                                                          *)

(* Compatibility of binary intersection with equivalence is well sorted.        *)
Proposition EquivCompat : CheckP (Inter2.env) Inter2.EquivCompat.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Inter2.EquivCompat. checkP.
Qed.

(* Left compatibility of binary intersection with equivalence is well sorted.   *)
Proposition EquivCompatL : CheckP (Inter2.env) Inter2.EquivCompatL.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Inter2.EquivCompatL. checkP.
Qed.

(* Right compatibility of binary intersection with equivalence is well sorted.  *)
Proposition EquivCompatR : CheckP (Inter2.env) Inter2.EquivCompatR.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Inter2.EquivCompatR. checkP.
Qed.

(* Compatibility of binary intersection with inclusion is well sorted.          *)
Proposition InclCompat : CheckP (Inter2.env) Inter2.InclCompat.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Inter2.InclCompat. checkP.
Qed.

(* Left compatibility of binary intersection with inclusion is well sorted.     *)
Proposition InclCompatL : CheckP (Inter2.env) Inter2.InclCompatL.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Inter2.InclCompatL. checkP.
Qed.

(* Right compatibility of binary intersection with inclusion is well sorted.    *)
Proposition InclCompatR : CheckP (Inter2.env) Inter2.InclCompatR.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Inter2.InclCompatR. checkP.
Qed.

(* Commutativity of binary intersection is well sorted.                         *)
Proposition Comm : CheckP (Inter2.env) Inter2.Comm.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Inter2.Comm. checkP.
Qed.

(* The left inclusion property of binary intersection is well sorted.           *)
Proposition IsInclL : CheckP (Inter2.env) Inter2.IsInclL.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Inter2.IsInclL. checkP.
Qed.

(* The right inclusion property of binary intersection is well sorted.          *)
Proposition IsInclR : CheckP (Inter2.env) Inter2.IsInclR.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Inter2.IsInclR. checkP.
Qed.

(* Left smallness of binary intersection is well sorted.                        *)
Proposition IsSmallL : CheckP (Inter2.env) Inter2.IsSmallL.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Inter2.IsSmallL. checkP.
Qed.

(* Right smallness of binary intersection is well sorted.                       *)
Proposition IsSmallR : CheckP (Inter2.env) Inter2.IsSmallR.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Inter2.IsSmallR. checkP.
Qed.

(* The universal property of binary intersection is well sorted.                *)
Proposition IsIncl : CheckP (Inter2.env) Inter2.IsIncl.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Inter2.IsIncl. checkP.
Qed.

(* The left inclusion characterization is well sorted.                          *)
Proposition WhenInclL : CheckP (Inter2.env) Inter2.WhenInclL.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Inter2.WhenInclL. checkP.
Qed.

(* The right inclusion characterization is well sorted.                         *)
Proposition WhenInclR : CheckP (Inter2.env) Inter2.WhenInclR.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Inter2.WhenInclR. checkP.
Qed.

(* Image inclusion through binary intersection is well sorted.                  *)
Proposition Image : CheckP (Inter2.env) Inter2.Image.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Inter2.Image. checkP.
Qed.
