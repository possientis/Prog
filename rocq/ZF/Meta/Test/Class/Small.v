Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

Require Import ZF.Meta.Check.Core.
Require Import ZF.Meta.Check.DeclP.
Require Import ZF.Meta.Check.DeclT.
Require Import ZF.Meta.DeclP.
Require Import ZF.Meta.Syntax.
Require Import ZF.Meta.Ty.

Require Import ZF.Meta.Decl.Class.Small.

Import ListNotations.
Open Scope string_scope.

(* Declaration typing.                                                          *)

(* The declaration body for smallness is well sorted.                           *)
Proposition Small : CheckT (Small.env) Small.Small.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  apply CheckEx, CheckAll, CheckIff.
  - apply CheckElem; apply CheckVar; reflexivity.
  - apply CheckApp.
    + apply CheckVar. reflexivity.
    + apply CheckVar. reflexivity.
Qed.

(* Proposition typing.                                                          *)

(* Smallness of the class associated with a set is well sorted.                 *)
Proposition SetIsSmall : CheckP (Small.env) Small.SetIsSmall.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  assert (Core.CheckT (Small.env) (ctxP Small.SetIsSmall)
    (conclP Small.SetIsSmall) TyProp) as H1. {
    apply CheckIdentT with [TyClass]. 1: reflexivity.
    apply CheckTsCons.
    - apply CheckIdentT with [TySet]. 1: reflexivity.
      apply CheckTsCons.
      + apply CheckVar. reflexivity.
      + apply CheckTsNil.
    - apply CheckTsNil. }
  split. 1: assumption. apply CheckHoleP. assumption.
Qed.

(* Equivalence with the class associated with a set is well sorted.             *)
Proposition IsSomeSet : CheckP (Small.env) Small.IsSomeSet.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  assert (Core.CheckT (Small.env) (ctxP Small.IsSomeSet)
    (conclP Small.IsSomeSet) TyProp) as H1. {
    apply CheckIff.
    - apply CheckIdentT with [TyClass]. 1: reflexivity.
      apply CheckTsCons.
      + apply CheckVar. reflexivity.
      + apply CheckTsNil.
    - apply CheckEx.
      apply CheckIdentT with [TyClass;TyClass]. 1: reflexivity.
      apply CheckTsCons.
      + apply CheckVar. reflexivity.
      + apply CheckTsCons.
        * apply CheckIdentT with [TySet]. 1: reflexivity.
          apply CheckTsCons.
          -- apply CheckVar. reflexivity.
          -- apply CheckTsNil.
        * apply CheckTsNil. }
  split. 1: assumption. apply CheckHoleP. assumption.
Qed.

(* Compatibility of smallness with equivalence is well sorted.                  *)
Proposition EquivCompat : CheckP (Small.env) Small.EquivCompat.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  assert (Core.CheckT (Small.env) (ctxP Small.EquivCompat)
    (conclP Small.EquivCompat) TyProp) as H1. {
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

(* Compatibility of smallness with inclusion is well sorted.                    *)
Proposition InclCompat : CheckP (Small.env) Small.InclCompat.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  assert (Core.CheckT (Small.env) (ctxP Small.InclCompat)
    (conclP Small.InclCompat) TyProp) as H1. {
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
