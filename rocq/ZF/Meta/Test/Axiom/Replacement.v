Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

Require Import ZF.Meta.Syntax.
Require Import ZF.Meta.Check.
Require Import ZF.Meta.CheckDeclP.
Require Import ZF.Meta.DeclP.
Require Import ZF.Meta.Ty.

Import ListNotations.
Open Scope string_scope.

Require Import ZF.Meta.Decl.Axiom.Replacement.

Proposition Replacement : CheckP (Replacement.env) Replacement.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  assert (Check.CheckT Replacement.env (ctxP Replacement)
    (conclP Replacement) TyProp) as H1. {
    apply CheckImp.
    - apply CheckIdentT with [TyClass]. 1: reflexivity.
      apply CheckTsCons.
      + apply CheckVar. reflexivity.
      + apply CheckTsNil.
    - apply CheckAll, CheckEx, CheckAll, CheckIff.
      + apply CheckElem; apply CheckVar; reflexivity.
      + apply CheckEx, CheckAnd.
        * apply CheckElem; apply CheckVar; reflexivity.
        * apply CheckApp.
          -- apply CheckVar. reflexivity.
          -- apply CheckIdentT with [TySet;TySet]. 1: reflexivity.
             apply CheckTsCons.
             ++ apply CheckVar. reflexivity.
             ++ apply CheckTsCons.
                ** apply CheckVar. reflexivity.
                ** apply CheckTsNil. }
  split. 1: assumption. apply CheckAxiomP. assumption.
Qed.
