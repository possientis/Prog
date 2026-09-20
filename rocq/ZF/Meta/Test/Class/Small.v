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

Require Import ZF.Meta.Decl.Class.Small.

Import ListNotations.
Open Scope string_scope.

(* Declaration typing.                                                          *)

(* The declaration body for smallness is well sorted.                           *)
Proposition Small : CheckT (Small.env) Small.Small.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Small.Small. checkT.
Qed.

(* Proposition typing.                                                          *)

(* Smallness of the class associated with a set is well sorted.                 *)
Proposition SetIsSmall : CheckP (Small.env) Small.SetIsSmall.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Small.SetIsSmall. checkP.
Qed.

(* Equivalence with the class associated with a set is well sorted.             *)
Proposition IsSomeSet : CheckP (Small.env) Small.IsSomeSet.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Small.IsSomeSet. checkP.
Qed.

(* Compatibility of smallness with equivalence is well sorted.                  *)
Proposition EquivCompat : CheckP (Small.env) Small.EquivCompat.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Small.EquivCompat. checkP.
Qed.

(* Compatibility of smallness with inclusion is well sorted.                    *)
Proposition InclCompat : CheckP (Small.env) Small.InclCompat.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Small.InclCompat. checkP.
Qed.
