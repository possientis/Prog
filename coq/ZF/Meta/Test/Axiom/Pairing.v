Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

Require Import ZF.Meta.Syntax.
Require Import ZF.Meta.Check.
Require Import ZF.Meta.Proof.CheckDecl.
Require Import ZF.Meta.Proof.Decl.
Require Import ZF.Meta.Ty.

Import ListNotations.
Open Scope string_scope.

Require Import ZF.Meta.Decl.Axiom.Pairing.

Proposition Pairing : CheckDeclP (Pairing.env) Pairing.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  assert (CheckT Pairing.env [] (conclP Pairing) TyProp) as H1. {
    apply CheckAll, CheckAll, CheckEx, CheckAll, CheckIff.
    - apply CheckElem; apply CheckVar; reflexivity.
    - apply CheckOr.
      + apply CheckEqual; apply CheckVar; reflexivity.
      + apply CheckEqual; apply CheckVar; reflexivity. }
  split. 1: assumption. apply CheckAxiomP. assumption.
Qed.
