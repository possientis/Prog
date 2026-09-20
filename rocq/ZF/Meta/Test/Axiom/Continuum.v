Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

Require Import ZF.Meta.Check.Core.
Require Import ZF.Meta.Check.DeclP.
Require Import ZF.Meta.Check.DeclT.
Require Import ZF.Meta.Check.Tactic.
Require Import ZF.Meta.SyntaxT.
Require Import ZF.Meta.SyntaxP.
Require Import ZF.Meta.Ty.

Import ListNotations.
Open Scope string_scope.

Require Import ZF.Meta.Decl.Axiom.Continuum.

Proposition CH : CheckT (Continuum.env) CH.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold CH. checkT.
Qed.

Proposition GCH : CheckT (Continuum.env) GCH.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold GCH. checkT.
Qed.

Proposition WhenGCH : CheckP (Continuum.env) WhenGCH.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold WhenGCH. checkP.
Qed.
