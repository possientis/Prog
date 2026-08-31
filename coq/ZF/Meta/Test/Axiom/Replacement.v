Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

Require Import ZF.Meta.Syntax.
Require Import ZF.Meta.Check.
Require Import ZF.Meta.Proof.CheckDecl.
Require Import ZF.Meta.Proof.Decl.
Require Import ZF.Meta.Ty.

Import ListNotations.

Require Import ZF.Meta.Decl.Axiom.Replacement.

Proposition Replacement : CheckDeclP (Replacement.env) Replacement.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  assert (CheckT Replacement.env (ctxP Replacement)
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
