Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

Require Import ZF.Meta.Syntax.
Require Import ZF.Meta.Check.Core.
Require Import ZF.Meta.Check.DeclP.
Require Import ZF.Meta.DeclP.
Require Import ZF.Meta.Ty.

Import ListNotations.
Open Scope string_scope.

Require Import ZF.Meta.Decl.Axiom.Pairing.

Proposition Pairing : CheckP (Pairing.env) Pairing.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  assert (Core.CheckT Pairing.env [] (conclP Pairing) TyProp) as H1. {
    apply CheckAll, CheckAll, CheckEx, CheckAll, CheckIff.
    - apply CheckElem; apply CheckVar; reflexivity.
    - apply CheckOr.
      + apply CheckEqual; apply CheckVar; reflexivity.
      + apply CheckEqual; apply CheckVar; reflexivity. }
  split. 1: assumption. apply CheckAxiomP. assumption.
Qed.
