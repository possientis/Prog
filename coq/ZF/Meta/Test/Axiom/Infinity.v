Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

Require Import ZF.Meta.Syntax.
Require Import ZF.Meta.Check.
Require Import ZF.Meta.Term.CheckDecl.
Require Import ZF.Meta.Ty.

Import ListNotations.

Require Import ZF.Meta.Decl.Axiom.Infinity.

Proposition Infinity : CheckDeclT (Infinity.env) Infinity.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
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
      * apply CheckVar. reflexivity.
Qed.
