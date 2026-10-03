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

Require Import ZF.Meta.Decl.Set.Relation.ImageUnderClass.

Import ListNotations.
Open Scope string_scope.

(* Declaration typing.                                                          *)

(* The declaration body for set image under a class is well sorted.             *)
Proposition image : CheckT (ImageUnderClass.env) ImageUnderClass.image.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold ImageUnderClass.image. checkT.
Qed.

(* Proposition typing.                                                          *)

(* The class image of a functional set image is well sorted.                    *)
Proposition ToClass : CheckP (ImageUnderClass.env) ImageUnderClass.ToClass.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold ImageUnderClass.ToClass. checkP.
Qed.

(* The class image of a small set image is well sorted.                         *)
Proposition ToClassWhenSmall : CheckP (ImageUnderClass.env) ImageUnderClass.ToClassWhenSmall.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold ImageUnderClass.ToClassWhenSmall. checkP.
Qed.

(* The forward characterization of set image is well sorted.                    *)
Proposition Charac : CheckP (ImageUnderClass.env) ImageUnderClass.Charac.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold ImageUnderClass.Charac. checkP.
Qed.

(* The reverse characterization of set image is well sorted.                    *)
Proposition CharacRev : CheckP (ImageUnderClass.env) ImageUnderClass.CharacRev.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold ImageUnderClass.CharacRev. checkP.
Qed.

(* Compatibility of set image with equivalence is well sorted.                  *)
Proposition EquivCompat : CheckP (ImageUnderClass.env) ImageUnderClass.EquivCompat.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold ImageUnderClass.EquivCompat. checkP.
Qed.

(* Compatibility of set image with inclusion is well sorted.                    *)
Proposition InclCompat : CheckP (ImageUnderClass.env) ImageUnderClass.InclCompat.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold ImageUnderClass.InclCompat. checkP.
Qed.

(* Left compatibility of set image with inclusion is well sorted.               *)
Proposition InclCompatL : CheckP (ImageUnderClass.env) ImageUnderClass.InclCompatL.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold ImageUnderClass.InclCompatL. checkP.
Qed.

(* Right compatibility of set image with inclusion is well sorted.              *)
Proposition InclCompatR : CheckP (ImageUnderClass.env) ImageUnderClass.InclCompatR.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold ImageUnderClass.InclCompatR. checkP.
Qed.

(* The image of an empty set being empty is well sorted.                        *)
Proposition WhenZero : CheckP (ImageUnderClass.env) ImageUnderClass.WhenZero.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold ImageUnderClass.WhenZero. checkP.
Qed.

(* The value-membership property of set image is well sorted.                   *)
Proposition IsIn : CheckP (ImageUnderClass.env) ImageUnderClass.IsIn.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold ImageUnderClass.IsIn. checkP.
Qed.
