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

Require Import ZF.Meta.Decl.Class.UnionGen.

Import ListNotations.
Open Scope string_scope.

(* Declaration typing.                                                          *)


(* The declaration body for generalized union is well sorted.                   *)
Proposition unionGen : CheckT (UnionGen.env) UnionGen.unionGen.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold UnionGen.unionGen. checkT.
Qed.

(* Proposition typing.                                                          *)

(* The element characterization of generalized union is well sorted.            *)
Proposition Charac : CheckP (UnionGen.env) UnionGen.Charac.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold UnionGen.Charac. checkP.
Qed.

(* Equality compatibility of generalized union is well sorted.                  *)
Proposition Equal : CheckP (UnionGen.env) UnionGen.Equal.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold UnionGen.Equal. checkP.
Qed.

(* Inclusion of each value in the generalized union is well sorted.             *)
Proposition IsIncl : CheckP (UnionGen.env) UnionGen.IsIncl.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold UnionGen.IsIncl. checkP.
Qed.

(* Smallness of generalized union over a small index class is well sorted.      *)
Proposition IsSmall : CheckP (UnionGen.env) UnionGen.IsSmall.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold UnionGen.IsSmall. checkP.
Qed.

(* Compatibility of generalized union with inclusion is well sorted.            *)
Proposition InclCompat : CheckP (UnionGen.env) UnionGen.InclCompat.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold UnionGen.InclCompat. checkP.
Qed.

(* Left inclusion compatibility of generalized union is well sorted.            *)
Proposition InclCompatL : CheckP (UnionGen.env) UnionGen.InclCompatL.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold UnionGen.InclCompatL. checkP.
Qed.

(* Right inclusion compatibility of generalized union is well sorted.           *)
Proposition InclCompatR : CheckP (UnionGen.env) UnionGen.InclCompatR.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold UnionGen.InclCompatR. checkP.
Qed.

(* The boundedness criterion for generalized union is well sorted.              *)
Proposition WhenBounded : CheckP (UnionGen.env) UnionGen.WhenBounded.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold UnionGen.WhenBounded. checkP.
Qed.
