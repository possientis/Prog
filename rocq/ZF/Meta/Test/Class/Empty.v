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

Require Import ZF.Meta.Decl.Class.Empty.

Import ListNotations.
Open Scope string_scope.

(* Declaration typing.                                                          *)

(* The declaration body for the empty class is well sorted.                     *)
Proposition empty : CheckT (Empty.env) Empty.empty.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Empty.empty. checkT.
Qed.

(* Proposition typing.                                                          *)

(* The characterization of the empty class is well sorted.                      *)
Proposition Charac : CheckP (Empty.env) Empty.Charac.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Empty.Charac. checkP.
Qed.

(* Smallness of the empty class is well sorted.                                 *)
Proposition IsSmall : CheckP (Empty.env) Empty.IsSmall.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Empty.IsSmall. checkP.
Qed.

(* The criterion for class non-emptiness is well sorted.                        *)
Proposition HasElem : CheckP (Empty.env) Empty.HasElem.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Empty.HasElem. checkP.
Qed.

(* The criterion for class emptiness is well sorted.                            *)
Proposition HasNoElem : CheckP (Empty.env) Empty.HasNoElem.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Empty.HasNoElem. checkP.
Qed.

(* The image of an empty class being empty is well sorted.                      *)
Proposition ImageOf : CheckP (Empty.env) Empty.ImageOf.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Empty.ImageOf. checkP.
Qed.

(* Inclusion into an empty class is well sorted.                                *)
Proposition WhenIncl : CheckP (Empty.env) Empty.WhenIncl.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Empty.WhenIncl. checkP.
Qed.
