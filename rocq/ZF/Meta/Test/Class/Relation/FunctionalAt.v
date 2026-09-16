Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

Require Import ZF.Meta.Check.Core.
Require Import ZF.Meta.Check.DeclP.
Require Import ZF.Meta.Check.DeclT.
Require Import ZF.Meta.DeclP.
Require Import ZF.Meta.Syntax.
Require Import ZF.Meta.Ty.

Require Import ZF.Meta.Decl.Class.Relation.FunctionalAt.

Import ListNotations.
Open Scope string_scope.

(* Declaration typing.                                                          *)

(* The declaration body for being functional at a point is well sorted.         *)
Proposition FunctionalAt : CheckT (FunctionalAt.env) FunctionalAt.FunctionalAt.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  apply CheckAll, CheckAll, CheckImp.
  - apply CheckApp.
    + apply CheckVar. reflexivity.
    + apply CheckIdentT with [TySet;TySet]. 1: reflexivity.
      apply CheckTsCons.
      * apply CheckVar. reflexivity.
      * apply CheckTsCons.
        -- apply CheckVar. reflexivity.
        -- apply CheckTsNil.
  - apply CheckImp.
    + apply CheckApp.
      * apply CheckVar. reflexivity.
      * apply CheckIdentT with [TySet;TySet]. 1: reflexivity.
        apply CheckTsCons.
        -- apply CheckVar. reflexivity.
        -- apply CheckTsCons.
           ++ apply CheckVar. reflexivity.
           ++ apply CheckTsNil.
    + apply CheckEqual; apply CheckVar; reflexivity.
Qed.

(* Proposition typing.                                                          *)

(* Compatibility of being functional at a point is well sorted.                 *)
Proposition EquivCompat : CheckP (FunctionalAt.env) FunctionalAt.EquivCompat.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  assert (Core.CheckT (FunctionalAt.env) (ctxP FunctionalAt.EquivCompat)
    (conclP FunctionalAt.EquivCompat) TyProp) as H1. {
    apply CheckImp.
    - apply CheckIdentT with [TyClass;TyClass]. 1: reflexivity.
      apply CheckTsCons.
      + apply CheckVar. reflexivity.
      + apply CheckTsCons.
        * apply CheckVar. reflexivity.
        * apply CheckTsNil.
    - apply CheckImp.
      + apply CheckIdentT with [TyClass;TySet]. 1: reflexivity.
        apply CheckTsCons.
        * apply CheckVar. reflexivity.
        * apply CheckTsCons.
          -- apply CheckVar. reflexivity.
          -- apply CheckTsNil.
      + apply CheckIdentT with [TyClass;TySet]. 1: reflexivity.
        apply CheckTsCons.
        * apply CheckVar. reflexivity.
        * apply CheckTsCons.
          -- apply CheckVar. reflexivity.
          -- apply CheckTsNil. }
  split. 1: assumption. apply CheckHoleP. assumption.
Qed.

(* The negation characterization is well sorted.                                *)
Proposition WhenNot : CheckP (FunctionalAt.env) FunctionalAt.WhenNot.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  assert (Core.CheckT (FunctionalAt.env) (ctxP FunctionalAt.WhenNot)
    (conclP FunctionalAt.WhenNot) TyProp) as H1. {
    apply CheckIff.
    - apply CheckNot.
      apply CheckIdentT with [TyClass;TySet]. 1: reflexivity.
      apply CheckTsCons.
      + apply CheckVar. reflexivity.
      + apply CheckTsCons.
        * apply CheckVar. reflexivity.
        * apply CheckTsNil.
    - apply CheckEx, CheckEx, CheckAnd.
      + apply CheckNotEq; apply CheckVar; reflexivity.
      + apply CheckAnd.
        * apply CheckApp.
          -- apply CheckVar. reflexivity.
          -- apply CheckIdentT with [TySet;TySet]. 1: reflexivity.
             apply CheckTsCons.
             ++ apply CheckVar. reflexivity.
             ++ apply CheckTsCons.
                ** apply CheckVar. reflexivity.
                ** apply CheckTsNil.
        * apply CheckApp.
          -- apply CheckVar. reflexivity.
          -- apply CheckIdentT with [TySet;TySet]. 1: reflexivity.
             apply CheckTsCons.
             ++ apply CheckVar. reflexivity.
             ++ apply CheckTsCons.
                ** apply CheckVar. reflexivity.
                ** apply CheckTsNil. }
  split. 1: assumption. apply CheckHoleP. assumption.
Qed.
