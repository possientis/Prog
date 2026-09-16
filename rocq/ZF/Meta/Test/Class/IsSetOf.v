Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

Require Import ZF.Meta.Check.Core.
Require Import ZF.Meta.Check.DeclP.
Require Import ZF.Meta.Check.DeclT.
Require Import ZF.Meta.DeclP.
Require Import ZF.Meta.Syntax.
Require Import ZF.Meta.Ty.

Require Import ZF.Meta.Decl.Class.IsSetOf.

Import ListNotations.
Open Scope string_scope.

(* Declaration typing.                                                          *)

(* The declaration body for sets defined by a class is well sorted.             *)
Proposition IsSetOf : CheckT (IsSetOf.env) IsSetOf.IsSetOf.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  apply CheckLam, CheckAll, CheckIff.
  - apply CheckElem; apply CheckVar; reflexivity.
  - apply CheckApp; apply CheckVar; reflexivity.
Qed.

(* Proposition typing.                                                          *)

(* Existence of a set defined by a small class is well sorted.                  *)
Proposition Exists : CheckP (IsSetOf.env) IsSetOf.Exists.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  assert (Core.CheckT (IsSetOf.env) (ctxP IsSetOf.Exists)
    (conclP IsSetOf.Exists) TyProp) as H1. {
    apply CheckImp.
    - apply CheckIdentT with [TyClass]. 1: reflexivity.
      apply CheckTsCons.
      + apply CheckVar. reflexivity.
      + apply CheckTsNil.
    - apply CheckIdentT with [TyClass]. 1: reflexivity.
      apply CheckTsCons.
      + apply CheckIdentT with [TyClass]. 1: reflexivity.
        apply CheckTsCons.
        * apply CheckVar. reflexivity.
        * apply CheckTsNil.
      + apply CheckTsNil. }
  split. 1: assumption. apply CheckHoleP. assumption.
Qed.

(* Uniqueness of a set defined by a class is well sorted.                       *)
Proposition Unique : CheckP (IsSetOf.env) IsSetOf.Unique.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  assert (Core.CheckT (IsSetOf.env) (ctxP IsSetOf.Unique)
    (conclP IsSetOf.Unique) TyProp) as H1. {
    apply CheckIdentT with [TyClass]. 1: reflexivity.
    apply CheckTsCons.
    - apply CheckIdentT with [TyClass]. 1: reflexivity.
      apply CheckTsCons.
      + apply CheckVar. reflexivity.
      + apply CheckTsNil.
    - apply CheckTsNil. }
  split. 1: assumption. apply CheckHoleP. assumption.
Qed.

(* Compatibility of sets defined by classes with equivalence is well sorted.    *)
Proposition EquivCompat : CheckP (IsSetOf.env) IsSetOf.EquivCompat.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  assert (Core.CheckT (IsSetOf.env) (ctxP IsSetOf.EquivCompat)
    (conclP IsSetOf.EquivCompat) TyProp) as H1. {
    apply CheckImp.
    - apply CheckIdentT with [TyClass;TyClass]. 1: reflexivity.
      apply CheckTsCons.
      + apply CheckVar. reflexivity.
      + apply CheckTsCons.
        * apply CheckVar. reflexivity.
        * apply CheckTsNil.
    - apply CheckIdentT with [TyClass;TyClass]. 1: reflexivity.
      apply CheckTsCons.
      + apply CheckIdentT with [TyClass]. 1: reflexivity.
        apply CheckTsCons.
        * apply CheckVar. reflexivity.
        * apply CheckTsNil.
      + apply CheckTsCons.
        * apply CheckIdentT with [TyClass]. 1: reflexivity.
          apply CheckTsCons.
          -- apply CheckVar. reflexivity.
          -- apply CheckTsNil.
        * apply CheckTsNil. }
  split. 1: assumption. apply CheckHoleP. assumption.
Qed.

(* The class of members of a defined set is well sorted.                        *)
Proposition ToClass : CheckP (IsSetOf.env) IsSetOf.ToClass.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  assert (Core.CheckT (IsSetOf.env) (ctxP IsSetOf.ToClass)
    (conclP IsSetOf.ToClass) TyProp) as H1. {
    apply CheckIff.
    - apply CheckApp.
      + apply CheckIdentT with [TyClass]. 1: reflexivity.
        apply CheckTsCons.
        * apply CheckVar. reflexivity.
        * apply CheckTsNil.
      + apply CheckVar. reflexivity.
    - apply CheckIdentT with [TyClass;TyClass]. 1: reflexivity.
      apply CheckTsCons.
      + apply CheckIdentT with [TySet]. 1: reflexivity.
        apply CheckTsCons.
        * apply CheckVar. reflexivity.
        * apply CheckTsNil.
      + apply CheckTsCons.
        * apply CheckVar. reflexivity.
        * apply CheckTsNil. }
  split. 1: assumption. apply CheckHoleP. assumption.
Qed.
