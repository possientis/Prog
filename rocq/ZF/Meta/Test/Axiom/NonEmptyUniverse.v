Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

Require Import ZF.Meta.Syntax.
Require Import ZF.Meta.Check.
Require Import ZF.Meta.CheckDeclP.
Require Import ZF.Meta.DeclP.
Require Import ZF.Meta.Ty.

Import ListNotations.
Open Scope string_scope.

Require Import ZF.Meta.Decl.Axiom.NonEmptyUniverse.

Proposition NonEmptyUniverse :
  CheckP (NonEmptyUniverse.env) NonEmptyUniverse.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  assert (Check.CheckT NonEmptyUniverse.env []
    (conclP NonEmptyUniverse) TyProp) as H1. { apply CheckEx, CheckTop. }
  split. 1: assumption. apply CheckAxiomP. assumption.
Qed.
