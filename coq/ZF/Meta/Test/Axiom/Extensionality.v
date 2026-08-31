Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

Require Import ZF.Meta.Syntax.
Require Import ZF.Meta.Check.
Require Import ZF.Meta.Proof.CheckDecl.
Require Import ZF.Meta.Proof.Decl.
Require Import ZF.Meta.Ty.

Import ListNotations.
Open Scope string_scope.

Require Import ZF.Meta.Decl.Axiom.Extensionality.

Proposition Extensionality : CheckDeclP (Extensionality.env) Extensionality.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  assert (CheckT Extensionality.env [] (conclP Extensionality) TyProp) as H1. {
    apply CheckAll, CheckAll, CheckImp.
    - apply CheckAll, CheckIff.
      + apply CheckElem; apply CheckVar; reflexivity.
      + apply CheckElem; apply CheckVar; reflexivity.
    - apply CheckEqual;  apply CheckVar; reflexivity. }
  split. 1: assumption. apply CheckAxiomP. assumption.
Qed.
