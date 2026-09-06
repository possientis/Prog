Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

Require Import ZF.Meta.Syntax.
Require Import ZF.Meta.Check.
Require Import ZF.Meta.CheckDeclP.
Require Import ZF.Meta.DeclP.
Require Import ZF.Meta.Ty.

Import ListNotations.
Open Scope string_scope.

Require Import ZF.Meta.Decl.Axiom.Specification.

Proposition Specification : CheckP (Specification.env) Specification.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  assert (Check.CheckT Specification.env (ctxP Specification)
    (conclP Specification) TyProp) as H1. {
    apply CheckAll, CheckEx, CheckAll, CheckIff.
    - apply CheckElem; apply CheckVar; reflexivity.
    - apply CheckAnd.
      + apply CheckElem; apply CheckVar; reflexivity.
      + apply CheckApp.
        * apply CheckVar. reflexivity.
        * apply CheckVar. reflexivity. }
  split. 1: assumption. apply CheckHoleP. assumption.
Qed.
