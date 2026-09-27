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

Require Import ZF.Meta.Decl.Class.Relation.Range.

Import ListNotations.
Open Scope string_scope.

(* Declaration typing.                                                          *)

(* The declaration body for relation range is well sorted.                      *)
Proposition range : CheckT (Range.env) Range.range.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Range.range. checkT.
Qed.

(* Proposition typing.                                                          *)

(* Compatibility of relation range with equivalence is well sorted.             *)
Proposition EquivCompat : CheckP (Range.env) Range.EquivCompat.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Range.EquivCompat. checkP.
Qed.

(* Compatibility of relation range with inclusion is well sorted.               *)
Proposition InclCompat : CheckP (Range.env) Range.InclCompat.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Range.InclCompat. checkP.
Qed.

(* The image-under-second-projection characterization is well sorted.           *)
Proposition ImageUnderSnd : CheckP (Range.env) Range.ImageUnderSnd.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Range.ImageUnderSnd. checkP.
Qed.

(* The image-of-domain characterization is well sorted.                         *)
Proposition ImageOfDomain : CheckP (Range.env) Range.ImageOfDomain.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Range.ImageOfDomain. checkP.
Qed.

(* Smallness of relation range over a small relation is well sorted.            *)
Proposition IsSmall : CheckP (Range.env) Range.IsSmall.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Range.IsSmall. checkP.
Qed.

(* Non-emptiness of range from non-emptiness of domain is well sorted.          *)
Proposition IsNotEmpty : CheckP (Range.env) Range.IsNotEmpty.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Range.IsNotEmpty. checkP.
Qed.

(* Direct-image inclusion into range is well sorted.                            *)
Proposition ImageIncl : CheckP (Range.env) Range.ImageIncl.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Range.ImageIncl. checkP.
Qed.
