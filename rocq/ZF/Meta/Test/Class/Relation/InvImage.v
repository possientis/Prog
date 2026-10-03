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

Require Import ZF.Meta.Decl.Class.Relation.InvImage.

Import ListNotations.
Open Scope string_scope.

(* Proposition typing.                                                          *)

(* The characterization of inverse image is well sorted.                        *)
Proposition Charac : CheckP (InvImage.env) InvImage.Charac.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold InvImage.Charac. checkP.
Qed.

(* Compatibility of inverse image with equivalence is well sorted.              *)
Proposition EquivCompat : CheckP (InvImage.env) InvImage.EquivCompat.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold InvImage.EquivCompat. checkP.
Qed.

(* Left compatibility of inverse image with equivalence is well sorted.         *)
Proposition EquivCompatL : CheckP (InvImage.env) InvImage.EquivCompatL.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold InvImage.EquivCompatL. checkP.
Qed.

(* Right compatibility of inverse image with equivalence is well sorted.        *)
Proposition EquivCompatR : CheckP (InvImage.env) InvImage.EquivCompatR.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold InvImage.EquivCompatR. checkP.
Qed.

(* Compatibility of inverse image with inclusion is well sorted.                *)
Proposition InclCompat : CheckP (InvImage.env) InvImage.InclCompat.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold InvImage.InclCompat. checkP.
Qed.

(* Left compatibility of inverse image with inclusion is well sorted.           *)
Proposition InclCompatL : CheckP (InvImage.env) InvImage.InclCompatL.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold InvImage.InclCompatL. checkP.
Qed.

(* Right compatibility of inverse image with inclusion is well sorted.          *)
Proposition InclCompatR : CheckP (InvImage.env) InvImage.InclCompatR.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold InvImage.InclCompatR. checkP.
Qed.

(* Inverse image of the range being the domain is well sorted.                  *)
Proposition OfRange : CheckP (InvImage.env) InvImage.OfRange.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold InvImage.OfRange. checkP.
Qed.

(* Evaluation characterization of inverse image is well sorted.                 *)
Proposition Eval : CheckP (InvImage.env) InvImage.Eval.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold InvImage.Eval. checkP.
Qed.

(* Preimage of image inclusion is well sorted.                                  *)
Proposition OfImageIsLess : CheckP (InvImage.env) InvImage.OfImageIsLess.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold InvImage.OfImageIsLess. checkP.
Qed.

(* Domain-bounded preimage of image inclusion is well sorted.                   *)
Proposition OfImageIsMore : CheckP (InvImage.env) InvImage.OfImageIsMore.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold InvImage.OfImageIsMore. checkP.
Qed.

(* Image of inverse image inclusion is well sorted.                             *)
Proposition ImageIsLess : CheckP (InvImage.env) InvImage.ImageIsLess.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold InvImage.ImageIsLess. checkP.
Qed.

(* Range-bounded image of inverse image inclusion is well sorted.               *)
Proposition ImageIsMore : CheckP (InvImage.env) InvImage.ImageIsMore.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold InvImage.ImageIsMore. checkP.
Qed.
