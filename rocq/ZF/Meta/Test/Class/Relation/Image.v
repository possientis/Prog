Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

Require Import ZF.Meta.Check.Core.
Require Import ZF.Meta.Check.DeclP.
Require Import ZF.Meta.Check.DeclT.
Require Import ZF.Meta.Check.Tactic.
Require Import ZF.Meta.DeclP.
Require Import ZF.Meta.Syntax.
Require Import ZF.Meta.Ty.

Require Import ZF.Meta.Decl.Class.Relation.Image.

Import ListNotations.
Open Scope string_scope.

(* Declaration typing.                                                          *)

(* The declaration body for direct image is well sorted.                        *)
Proposition image : CheckT (Image.env) Image.image.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Image.image. checkT.
Qed.

(* Proposition typing.                                                          *)

(* Compatibility of direct image with equivalence is well sorted.               *)
Proposition EquivCompat : CheckP (Image.env) Image.EquivCompat.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Image.EquivCompat. checkP.
Qed.

(* Left compatibility of direct image with equivalence is well sorted.          *)
Proposition EquivCompatL : CheckP (Image.env) Image.EquivCompatL.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Image.EquivCompatL. checkP.
Qed.

(* Right compatibility of direct image with equivalence is well sorted.         *)
Proposition EquivCompatR : CheckP (Image.env) Image.EquivCompatR.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Image.EquivCompatR. checkP.
Qed.

(* Compatibility of direct image with inclusion is well sorted.                 *)
Proposition InclCompat : CheckP (Image.env) Image.InclCompat.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Image.InclCompat. checkP.
Qed.

(* Left compatibility of direct image with inclusion is well sorted.            *)
Proposition InclCompatL : CheckP (Image.env) Image.InclCompatL.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Image.InclCompatL. checkP.
Qed.

(* Right compatibility of direct image with inclusion is well sorted.           *)
Proposition InclCompatR : CheckP (Image.env) Image.InclCompatR.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Image.InclCompatR. checkP.
Qed.

(* Smallness of the right direct image of a functional class is well sorted.    *)
Proposition IsSmallR : CheckP (Image.env) Image.IsSmallR.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Image.IsSmallR. checkP.
Qed.

(* Smallness of the left direct image of a small class is well sorted.          *)
Proposition IsSmallL : CheckP (Image.env) Image.IsSmallL.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Image.IsSmallL. checkP.
Qed.
