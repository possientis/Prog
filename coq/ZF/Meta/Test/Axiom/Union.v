Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

Require Import ZF.Meta.Syntax.
Require Import ZF.Meta.Check.
Require Import ZF.Meta.Proof.CheckDecl.
Require Import ZF.Meta.Proof.Decl.
Require Import ZF.Meta.Ty.

Import ListNotations.

Require Import ZF.Meta.Decl.Axiom.Union.

Proposition Union : CheckDeclP (Union.env) Union.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  assert (CheckT Union.env [] (conclP Union) TyProp) as H1. {
    apply CheckAll, CheckEx, CheckAll, CheckIff.
    - apply CheckElem; apply CheckVar; reflexivity.
    - apply CheckEx, CheckAnd.
      + apply CheckElem; apply CheckVar; reflexivity.
      + apply CheckElem; apply CheckVar; reflexivity. }
  split. 1: assumption. apply CheckAxiomP. assumption.
Qed.
