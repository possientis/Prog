Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

Require Import ZF.Meta.Syntax.
Require Import ZF.Meta.Check.
Require Import ZF.Meta.Proof.CheckDecl.
Require Import ZF.Meta.Proof.Decl.
Require Import ZF.Meta.Ty.

Import ListNotations.

Require Import ZF.Meta.Decl.Axiom.Foundation.

Proposition Foundation : CheckDeclP (Foundation.env) Foundation.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  assert (CheckT Foundation.env [] (conclP Foundation) TyProp) as H1. {
    apply CheckAll, CheckImp.
    - apply CheckNotEq.
      + apply CheckVar. reflexivity.
      + apply CheckIdentT with []. 1: reflexivity.
        apply CheckTsNil.
    - apply CheckEx, CheckAnd.
      + apply CheckElem; apply CheckVar; reflexivity.
      + apply CheckEqual.
        * apply CheckIdentT with [TySet;TySet]. 1: reflexivity.
          apply CheckTsCons.
          -- apply CheckVar. reflexivity.
          -- apply CheckTsCons.
             ++ apply CheckVar. reflexivity.
             ++ apply CheckTsNil.
        * apply CheckIdentT with []. 1: reflexivity.
          apply CheckTsNil. }
  split. 1: assumption. apply CheckAxiomP. assumption.
Qed.
