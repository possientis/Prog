Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

Require Import ZF.Meta.Check.
Require Import ZF.Meta.Term.CheckDecl.
Require Import ZF.Meta.Syntax.
Require Import ZF.Meta.Ty.

Import ListNotations.
Open Scope string_scope.

Require Import ZF.Meta.Decl.Axiom.Choice.

Proposition Choice : CheckDeclT (Choice.env) Choice.
Proof.
  apply CheckAll, CheckEx, CheckAnd.
  - apply CheckIdentT with [TySet;TySet]. 1: reflexivity.
    apply CheckTsCons.
    + apply CheckVar. reflexivity.
    + apply CheckTsCons.
      * apply CheckVar. reflexivity.
      * apply CheckTsNil.
  - apply CheckAll, CheckImp.
    + apply CheckElem; apply CheckVar; reflexivity.
    + apply CheckImp.
      * apply CheckNotEq.
        -- apply CheckVar. reflexivity.
        -- apply CheckIdentT with []. 1: reflexivity.
           apply CheckTsNil.
      * apply CheckElem.
        -- apply CheckIdentT with [TySet;TySet]. 1: reflexivity.
           apply CheckTsCons.
           ++ apply CheckVar. reflexivity.
           ++ apply CheckTsCons.
              ** apply CheckVar. reflexivity.
              ** apply CheckTsNil.
        -- apply CheckVar. reflexivity.
Qed.
