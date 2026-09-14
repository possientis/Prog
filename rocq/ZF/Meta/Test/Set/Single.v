Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

Require Import ZF.Meta.Check.Core.
Require Import ZF.Meta.Check.DeclP.
Require Import ZF.Meta.Check.DeclT.
Require Import ZF.Meta.DeclP.
Require Import ZF.Meta.Syntax.
Require Import ZF.Meta.Ty.

Require Import ZF.Meta.Decl.Set.Single.

Import ListNotations.
Open Scope string_scope.

(* Declaration typing.                                                          *)

(* The singleton declaration is the pair of a set with itself.                  *)
Proposition single : CheckT (Single.env) Single.single.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  apply CheckIdentT with [TySet;TySet]. 1: reflexivity.
  apply CheckTsCons.
  - apply CheckVar. reflexivity.
  - apply CheckTsCons.
    + apply CheckVar. reflexivity.
    + apply CheckTsNil.
Qed.

(* The characterization proposition is well sorted.                             *)
Proposition Charac : CheckP (Single.env) Single.Charac.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  assert (Core.CheckT (Single.env) (ctxP Single.Charac)
    (conclP Single.Charac) TyProp) as H1. {
    apply CheckAll, CheckAll, CheckIff.
    - apply CheckElem.
      + apply CheckVar. reflexivity.
      + apply CheckIdentT with [TySet]. 1: reflexivity.
        apply CheckTsCons.
        * apply CheckVar. reflexivity.
        * apply CheckTsNil.
    - apply CheckEqual; apply CheckVar; reflexivity. }
  split. 1: assumption. apply CheckHoleP. assumption.
Qed.

(* The membership proposition is well sorted.                                   *)
Proposition IsIn : CheckP (Single.env) Single.IsIn.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  assert (Core.CheckT (Single.env) (ctxP Single.IsIn)
    (conclP Single.IsIn) TyProp) as H1. {
    apply CheckAll, CheckElem.
    - apply CheckVar. reflexivity.
    - apply CheckIdentT with [TySet]. 1: reflexivity.
      apply CheckTsCons.
      + apply CheckVar. reflexivity.
      + apply CheckTsNil. }
  split. 1: assumption. apply CheckHoleP. assumption.
Qed.

(* Equality of singletons implies equality of their members.                    *)
Proposition WhenEqual : CheckP (Single.env) Single.WhenEqual.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  assert (Core.CheckT (Single.env) (ctxP Single.WhenEqual)
    (conclP Single.WhenEqual) TyProp) as H1. {
    apply CheckAll, CheckAll, CheckImp.
    - apply CheckEqual.
      + apply CheckIdentT with [TySet]. 1: reflexivity.
        apply CheckTsCons.
        * apply CheckVar. reflexivity.
        * apply CheckTsNil.
      + apply CheckIdentT with [TySet]. 1: reflexivity.
        apply CheckTsCons.
        * apply CheckVar. reflexivity.
        * apply CheckTsNil.
    - apply CheckEqual; apply CheckVar; reflexivity. }
  split. 1: assumption. apply CheckHoleP. assumption.
Qed.

(* The class-inclusion proposition is well sorted.                              *)
Proposition ToClassIncl : CheckP (Single.env) Single.ToClassIncl.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  assert (Core.CheckT (Single.env) (ctxP Single.ToClassIncl)
    (conclP Single.ToClassIncl) TyProp) as H1. {
    apply CheckAll, CheckIff.
    - apply CheckApp.
      + apply CheckVar. reflexivity.
      + apply CheckVar. reflexivity.
    - apply CheckIdentT with [TyClass;TyClass]. 1: reflexivity.
      apply CheckTsCons.
      + apply CheckIdentT with [TySet]. 1: reflexivity.
        apply CheckTsCons.
        * apply CheckIdentT with [TySet]. 1: reflexivity.
          apply CheckTsCons.
          -- apply CheckVar. reflexivity.
          -- apply CheckTsNil.
        * apply CheckTsNil.
      + apply CheckTsCons.
        * apply CheckVar. reflexivity.
        * apply CheckTsNil. }
  split. 1: assumption. apply CheckHoleP. assumption.
Qed.

(* The singleton-not-pair proposition is well sorted.                           *)
Proposition IsNotPair : CheckP (Single.env) Single.IsNotPair.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  assert (Core.CheckT (Single.env) (ctxP Single.IsNotPair)
    (conclP Single.IsNotPair) TyProp) as H1. {
    apply CheckAll, CheckAll, CheckAll, CheckImp.
    - apply CheckNotEq; apply CheckVar; reflexivity.
    - apply CheckNotEq.
      + apply CheckIdentT with [TySet]. 1: reflexivity.
        apply CheckTsCons.
        * apply CheckVar. reflexivity.
        * apply CheckTsNil.
      + apply CheckIdentT with [TySet;TySet]. 1: reflexivity.
        apply CheckTsCons.
        * apply CheckVar. reflexivity.
        * apply CheckTsCons.
          -- apply CheckVar. reflexivity.
          -- apply CheckTsNil. }
  split. 1: assumption. apply CheckHoleP. assumption.
Qed.
