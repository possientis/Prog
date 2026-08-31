Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

Require Import ZF.Meta.Syntax.
Require Import ZF.Meta.Check.
Require Import ZF.Meta.Proof.CheckDecl.
Require Import ZF.Meta.Proof.Decl.
Require Import ZF.Meta.Ty.

Import ListNotations.
Open Scope string_scope.

Require Import ZF.Meta.Decl.Axiom.NonEmptyUniverse.

Proposition NonEmptyUniverse :
  CheckDeclP (NonEmptyUniverse.env) NonEmptyUniverse.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  assert (CheckT NonEmptyUniverse.env []
    (conclP NonEmptyUniverse) TyProp) as H1. { apply CheckEx, CheckTop. }
  split. 1: assumption. apply CheckAxiomP. assumption.
Qed.
