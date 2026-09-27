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

Require Import ZF.Meta.Decl.Class.V.

Import ListNotations.
Open Scope string_scope.

(* Declaration typing.                                                          *)

(* The declaration body for the universal class is well sorted.                 *)
Proposition V : CheckT (V.env) V.V.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold V.V. checkT.
Qed.

(* Proposition typing.                                                          *)

(* Every class being included in V is well sorted.                              *)
Proposition IsIncl : CheckP (V.env) V.IsIncl.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold V.IsIncl. checkP.
Qed.

(* The left-intersection identity for V is well sorted.                         *)
Proposition Inter2VL : CheckP (V.env) V.Inter2VL.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold V.Inter2VL. checkP.
Qed.

(* The right-intersection identity for V is well sorted.                        *)
Proposition Inter2VR : CheckP (V.env) V.Inter2VR.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold V.Inter2VR. checkP.
Qed.

(* Properness of V is well sorted.                                              *)
Proposition IsProper : CheckP (V.env) V.IsProper.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold V.IsProper. checkP.
Qed.

(* Properness of V squared is well sorted.                                      *)
Proposition V2IsProper : CheckP (V.env) V.V2IsProper.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold V.V2IsProper. checkP.
Qed.

(* Inclusion of class products in V squared is well sorted.                     *)
Proposition ProdInclV2 : CheckP (V.env) V.ProdInclV2.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold V.ProdInclV2. checkP.
Qed.

(* Strict inclusion of V squared in V is well sorted.                           *)
Proposition IsLess : CheckP (V.env) V.IsLess.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold V.IsLess. checkP.
Qed.

