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

Require Import ZF.Meta.Decl.Set.Union2.

Import ListNotations.
Open Scope string_scope.

(* Declaration typing.                                                          *)

(* The declaration body for binary set union is well sorted.                    *)
Proposition union2 : CheckT (Union2.env) Union2.union2.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Union2.union2. checkT.
Qed.

(* Proposition typing.                                                          *)

(* The characterization of binary set union is well sorted.                     *)
Proposition Charac : CheckP (Union2.env) Union2.Charac.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Union2.Charac. checkP.
Qed.

(* Commutativity of binary set union is well sorted.                            *)
Proposition Comm : CheckP (Union2.env) Union2.Comm.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Union2.Comm. checkP.
Qed.

(* Associativity of binary set union is well sorted.                            *)
Proposition Assoc : CheckP (Union2.env) Union2.Assoc.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Union2.Assoc. checkP.
Qed.

(* Compatibility of binary set union with inclusion is well sorted.             *)
Proposition InclCompat : CheckP (Union2.env) Union2.InclCompat.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Union2.InclCompat. checkP.
Qed.

(* Left compatibility of binary set union with inclusion is well sorted.        *)
Proposition InclCompatL : CheckP (Union2.env) Union2.InclCompatL.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Union2.InclCompatL. checkP.
Qed.

(* Right compatibility of binary set union with inclusion is well sorted.       *)
Proposition InclCompatR : CheckP (Union2.env) Union2.InclCompatR.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Union2.InclCompatR. checkP.
Qed.

(* The right absorption criterion for binary set union is well sorted.          *)
Proposition WhenEqualR : CheckP (Union2.env) Union2.WhenEqualR.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Union2.WhenEqualR. checkP.
Qed.

(* The left absorption criterion for binary set union is well sorted.           *)
Proposition WhenEqualL : CheckP (Union2.env) Union2.WhenEqualL.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Union2.WhenEqualL. checkP.
Qed.

(* The left inclusion property of binary set union is well sorted.              *)
Proposition IsInclL : CheckP (Union2.env) Union2.IsInclL.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Union2.IsInclL. checkP.
Qed.

(* The right inclusion property of binary set union is well sorted.             *)
Proposition IsInclR : CheckP (Union2.env) Union2.IsInclR.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Union2.IsInclR. checkP.
Qed.

(* The unordered-pair-as-union characterization is well sorted.                 *)
Proposition AsPair : CheckP (Union2.env) Union2.AsPair.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Union2.AsPair. checkP.
Qed.

(* The left identity property of binary set union is well sorted.               *)
Proposition IdentityL : CheckP (Union2.env) Union2.IdentityL.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Union2.IdentityL. checkP.
Qed.

(* The right identity property of binary set union is well sorted.              *)
Proposition IdentityR : CheckP (Union2.env) Union2.IdentityR.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Union2.IdentityR. checkP.
Qed.

(* The universal inclusion property of binary set union is well sorted.         *)
Proposition IsIncl : CheckP (Union2.env) Union2.IsIncl.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Union2.IsIncl. checkP.
Qed.

(* The three-way characterization of binary set union is well sorted.           *)
Proposition Charac3 : CheckP (Union2.env) Union2.Charac3.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Union2.Charac3. checkP.
Qed.
