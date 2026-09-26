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

Require Import ZF.Meta.Decl.Class.Inter.

Import ListNotations.
Open Scope string_scope.

(* Declaration typing.                                                          *)

(* The declaration body for class intersection is well sorted.                  *)
Proposition inter : CheckT (Inter.env) Inter.inter.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Inter.inter. checkT.
Qed.

(* The declaration body for non-empty-style class intersection is well sorted.  *)
Proposition inter' : CheckT (Inter.env) Inter.inter'.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Inter.inter'. checkT.
Qed.

(* Proposition typing.                                                          *)

(* Intersection of an empty class being empty is well sorted.                   *)
Proposition WhenZero : CheckP (Inter.env) Inter.WhenZero.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Inter.WhenZero. checkP.
Qed.

(* Intersection of the empty class being empty is well sorted.                  *)
Proposition IsZero : CheckP (Inter.env) Inter.IsZero.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Inter.IsZero. checkP.
Qed.

(* The non-empty characterization of intersection is well sorted.               *)
Proposition WhenNotZero : CheckP (Inter.env) Inter.WhenNotZero.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Inter.WhenNotZero. checkP.
Qed.

(* Compatibility of inter' with equivalence is well sorted.                     *)
Proposition EquivCompat' : CheckP (Inter.env) Inter.EquivCompat'.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Inter.EquivCompat'. checkP.
Qed.

(* Compatibility of intersection with equivalence is well sorted.               *)
Proposition EquivCompat : CheckP (Inter.env) Inter.EquivCompat.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Inter.EquivCompat. checkP.
Qed.

(* The inclusion property of inter' is well sorted.                             *)
Proposition IsIncl' : CheckP (Inter.env) Inter.IsIncl'.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Inter.IsIncl'. checkP.
Qed.

(* Smallness of inter' for a non-empty class is well sorted.                    *)
Proposition IsSmall' : CheckP (Inter.env) Inter.IsSmall'.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Inter.IsSmall'. checkP.
Qed.

(* Smallness of intersection is well sorted.                                    *)
Proposition IsSmall : CheckP (Inter.env) Inter.IsSmall.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Inter.IsSmall. checkP.
Qed.
