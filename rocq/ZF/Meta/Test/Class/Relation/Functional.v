Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

Require Import ZF.Meta.Check.Core.
Require Import ZF.Meta.Check.DeclP.
Require Import ZF.Meta.Check.DeclT.
Require Import ZF.Meta.DeclP.
Require Import ZF.Meta.Syntax.
Require Import ZF.Meta.Ty.

Require Import ZF.Meta.Decl.Class.Relation.Functional.

Import ListNotations.
Open Scope string_scope.

(* Declaration typing.                                                          *)

(* The declaration body for being functional is well sorted.                    *)
Proposition Functional : CheckT (Functional.env) Functional.Functional.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  apply CheckAll, CheckAll, CheckAll, CheckImp.
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

(* Compatibility of functionality with equivalence is well sorted.              *)
Proposition EquivCompat : CheckP (Functional.env) Functional.EquivCompat.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  assert (Core.CheckT (Functional.env) (ctxP Functional.EquivCompat)
    (conclP Functional.EquivCompat) TyProp) as H1. {
    apply CheckImp.
    - apply CheckIdentT with [TyClass;TyClass]. 1: reflexivity.
      apply CheckTsCons.
      + apply CheckVar. reflexivity.
      + apply CheckTsCons.
        * apply CheckVar. reflexivity.
        * apply CheckTsNil.
    - apply CheckImp.
      + apply CheckIdentT with [TyClass]. 1: reflexivity.
        apply CheckTsCons.
        * apply CheckVar. reflexivity.
        * apply CheckTsNil.
      + apply CheckIdentT with [TyClass]. 1: reflexivity.
        apply CheckTsCons.
        * apply CheckVar. reflexivity.
        * apply CheckTsNil. }
  split. 1: assumption. apply CheckHoleP. assumption.
Qed.

(* Compatibility of functionality with inclusion is well sorted.                *)
Proposition InclCompat : CheckP (Functional.env) Functional.InclCompat.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  assert (Core.CheckT (Functional.env) (ctxP Functional.InclCompat)
    (conclP Functional.InclCompat) TyProp) as H1. {
    apply CheckImp.
    - apply CheckIdentT with [TyClass;TyClass]. 1: reflexivity.
      apply CheckTsCons.
      + apply CheckVar. reflexivity.
      + apply CheckTsCons.
        * apply CheckVar. reflexivity.
        * apply CheckTsNil.
    - apply CheckImp.
      + apply CheckIdentT with [TyClass]. 1: reflexivity.
        apply CheckTsCons.
        * apply CheckVar. reflexivity.
        * apply CheckTsNil.
      + apply CheckIdentT with [TyClass]. 1: reflexivity.
        apply CheckTsCons.
        * apply CheckVar. reflexivity.
        * apply CheckTsNil. }
  split. 1: assumption. apply CheckHoleP. assumption.
Qed.

(* Characterization by pointwise functionality is well sorted.                  *)
Proposition IsFunctionalAt : CheckP (Functional.env) Functional.IsFunctionalAt.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  assert (Core.CheckT (Functional.env) (ctxP Functional.IsFunctionalAt)
    (conclP Functional.IsFunctionalAt) TyProp) as H1. {
    apply CheckIff.
    - apply CheckIdentT with [TyClass]. 1: reflexivity.
      apply CheckTsCons.
      + apply CheckVar. reflexivity.
      + apply CheckTsNil.
    - apply CheckAll.
      apply CheckIdentT with [TyClass;TySet]. 1: reflexivity.
      apply CheckTsCons.
      + apply CheckVar. reflexivity.
      + apply CheckTsCons.
        * apply CheckVar. reflexivity.
        * apply CheckTsNil. }
  split. 1: assumption. apply CheckHoleP. assumption.
Qed.
