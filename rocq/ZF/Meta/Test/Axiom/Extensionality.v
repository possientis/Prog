Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

Require Import ZF.Meta.Check.Core.
Require Import ZF.Meta.Check.DeclP.
Require Import ZF.Meta.Check.Tactic.
Require Import ZF.Meta.DeclP.
Require Import ZF.Meta.Syntax.
Require Import ZF.Meta.Ty.

Import ListNotations.
Open Scope string_scope.

Require Import ZF.Meta.Decl.Axiom.Extensionality.

Proposition Extensionality : CheckP (Extensionality.env) Extensionality.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  unfold Extensionality. checkP.
Qed.
