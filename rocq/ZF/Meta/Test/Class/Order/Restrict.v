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

Require Import ZF.Meta.Decl.Class.Order.Restrict.

Import ListNotations.
Open Scope string_scope.

(* Declaration typing.                                                          *)


(* The declaration body for order restriction is well sorted.                   *)
Proposition restrict : CheckT (Restrict.env) Restrict.restrict.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Restrict.restrict. checkT.
Qed.

(* Proposition typing.                                                          *)

(* The ordered-pair characterization of order restriction is well sorted.       *)
Proposition Charac2 : CheckP (Restrict.env) Restrict.Charac2.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Restrict.Charac2. checkP.
Qed.

(* Relationhood of order restriction is well sorted.                            *)
Proposition IsRelation : CheckP (Restrict.env) Restrict.IsRelation.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Restrict.IsRelation. checkP.
Qed.

(* Inclusion of order restriction in the original relation is well sorted.      *)
Proposition InclR : CheckP (Restrict.env) Restrict.InclR.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Restrict.InclR. checkP.
Qed.

(* Left membership from order restriction is well sorted.                       *)
Proposition InAL : CheckP (Restrict.env) Restrict.InAL.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Restrict.InAL. checkP.
Qed.

(* Right membership from order restriction is well sorted.                      *)
Proposition InAR : CheckP (Restrict.env) Restrict.InAR.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Restrict.InAR. checkP.
Qed.
