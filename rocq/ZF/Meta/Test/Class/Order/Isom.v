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

Require Import ZF.Meta.Decl.Class.Order.Isom.

Import ListNotations.
Open Scope string_scope.

(* Declaration typing.                                                          *)

(* The isomorphism declaration body is well sorted.                             *)
Proposition Isom : CheckT (Isom.env) Isom.Isom.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Isom.Isom. checkT.
Qed.

(* Proposition typing.                                                          *)

(* Equivalence compatibility for Isom is well sorted.                           *)
Proposition EquivCompat : CheckP (Isom.env) Isom.EquivCompat.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Isom.EquivCompat. checkP.
Qed.

(* First-argument equivalence compatibility for Isom is well sorted.            *)
Proposition EquivCompat1 : CheckP (Isom.env) Isom.EquivCompat1.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Isom.EquivCompat1. checkP.
Qed.

(* Second-argument equivalence compatibility for Isom is well sorted.           *)
Proposition EquivCompat2 : CheckP (Isom.env) Isom.EquivCompat2.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Isom.EquivCompat2. checkP.
Qed.

(* Third-argument equivalence compatibility for Isom is well sorted.            *)
Proposition EquivCompat3 : CheckP (Isom.env) Isom.EquivCompat3.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Isom.EquivCompat3. checkP.
Qed.

(* Fourth-argument equivalence compatibility for Isom is well sorted.           *)
Proposition EquivCompat4 : CheckP (Isom.env) Isom.EquivCompat4.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Isom.EquivCompat4. checkP.
Qed.

(* Fifth-argument equivalence compatibility for Isom is well sorted.            *)
Proposition EquivCompat5 : CheckP (Isom.env) Isom.EquivCompat5.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Isom.EquivCompat5. checkP.
Qed.

(* Source-relation restriction for Isom is well sorted.                         *)
Proposition RestrictL : CheckP (Isom.env) Isom.RestrictL.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Isom.RestrictL. checkP.
Qed.

(* Target-relation restriction for Isom is well sorted.                         *)
Proposition RestrictR : CheckP (Isom.env) Isom.RestrictR.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Isom.RestrictR. checkP.
Qed.

(* Converse closure for Isom is well sorted.                                    *)
Proposition Converse : CheckP (Isom.env) Isom.Converse.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Isom.Converse. checkP.
Qed.

(* Composition closure for Isom is well sorted.                                 *)
Proposition Compose : CheckP (Isom.env) Isom.Compose.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Isom.Compose. checkP.
Qed.

(* Transport construction of an isomorphism is well sorted.                     *)
Proposition Transport : CheckP (Isom.env) Isom.Transport.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Isom.Transport. checkP.
Qed.

