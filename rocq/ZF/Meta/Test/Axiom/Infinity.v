Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

Require Import ZF.Meta.Syntax.
Require Import ZF.Meta.Check.Core.
Require Import ZF.Meta.Check.DeclP.
Require Import ZF.Meta.DeclP.
Require Import ZF.Meta.Ty.

Import ListNotations.
Open Scope string_scope.

Require Import ZF.Meta.Decl.Axiom.Infinity.

Proposition Infinity : CheckP (Infinity.env) Infinity.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  assert (Core.CheckT Infinity.env [] (conclP Infinity) TyProp) as H1. {
    apply CheckEx, CheckAnd.
    - apply CheckElem.
      + apply CheckIdentT with []. 1: reflexivity.
        apply CheckTsNil.
      + apply CheckVar. reflexivity.
    - apply CheckAll, CheckImp.
      + apply CheckElem; apply CheckVar; reflexivity.
      + apply CheckElem.
        * apply CheckIdentT with [TySet;TySet]. 1: reflexivity.
          apply CheckTsCons.
          -- apply CheckVar. reflexivity.
          -- apply CheckTsCons.
             ++ apply CheckIdentT with [TySet]. 1: reflexivity.
                apply CheckTsCons.
                ** apply CheckVar. reflexivity.
                ** apply CheckTsNil.
             ++ apply CheckTsNil.
        * apply CheckVar. reflexivity. }
  split. 1: assumption. apply CheckAxiomP. assumption.
Qed.
