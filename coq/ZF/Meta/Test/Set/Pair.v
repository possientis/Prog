Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

Require Import ZF.Meta.Check.
Require Import ZF.Meta.Proof.CheckDecl.
Require Import ZF.Meta.Proof.Decl.
Require Import ZF.Meta.Syntax.
Require Import ZF.Meta.Term.CheckDecl.
Require Import ZF.Meta.Ty.

Require Import ZF.Meta.Decl.Set.Pair.

Import ListNotations.
Open Scope string_scope.

(* Declaration typing.                                                          *)

(* The declaration body for IsPairOf recognizes the two selected sets.          *)
Proposition IsPairOf : CheckDeclT (Pair.env) Pair.IsPairOf.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  apply CheckLam, CheckAll, CheckIff.
  - apply CheckElem; apply CheckVar; reflexivity.
  - apply CheckOr; apply CheckEqual; apply CheckVar; reflexivity.
Qed.

(* The existence proof declaration is well sorted.                              *)
Proposition Exists : CheckDeclP (Pair.env) Pair.Exists.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  assert (CheckT (Pair.env) (ctxP Pair.Exists)
    (conclP Pair.Exists) TyProp) as H1. {
    apply CheckEx, CheckApp.
    - apply CheckIdentT with [TySet;TySet]. 1: reflexivity.
      apply CheckTsCons.
      + apply CheckVar. reflexivity.
      + apply CheckTsCons.
        * apply CheckVar. reflexivity.
        * apply CheckTsNil.
    - apply CheckVar. reflexivity. }
  split. 1: assumption. apply CheckHoleP. assumption.
Qed.

(* The uniqueness proof declaration is well sorted.                             *)
Proposition Unique : CheckDeclP (Pair.env) Pair.Unique.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  assert (CheckT (Pair.env) (ctxP Pair.Unique)
    (conclP Pair.Unique) TyProp) as H1. {
    apply CheckAll, CheckAll, CheckImp.
    - apply CheckApp.
      + apply CheckIdentT with [TySet;TySet]. 1: reflexivity.
        apply CheckTsCons.
        * apply CheckVar. reflexivity.
        * apply CheckTsCons.
          -- apply CheckVar. reflexivity.
          -- apply CheckTsNil.
      + apply CheckVar. reflexivity.
    - apply CheckImp.
      + apply CheckApp.
        * apply CheckIdentT with [TySet;TySet]. 1: reflexivity.
          apply CheckTsCons.
          -- apply CheckVar. reflexivity.
          -- apply CheckTsCons.
             ++ apply CheckVar. reflexivity.
             ++ apply CheckTsNil.
        * apply CheckVar. reflexivity.
      + apply CheckEqual; apply CheckVar; reflexivity. }
  split. 1: assumption. apply CheckHoleP. assumption.
Qed.

(* The declaration body for pair denotes a set backed by proof references.      *)
Proposition pair : CheckDeclT (Pair.env) Pair.pair.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  apply CheckDef.
  - apply CheckIdentT with [TySet;TySet]. 1: reflexivity.
    apply CheckTsCons.
    + apply CheckVar. reflexivity.
    + apply CheckTsCons.
      * apply CheckVar. reflexivity.
      * apply CheckTsNil.
  - apply CheckIdentP with
      (tys := [TySet;TySet]) (t := conclP ZF.Meta.Decl.Set.Pair.Exists).
    1: reflexivity.
    apply CheckTsCons.
    + apply CheckVar. reflexivity.
    + apply CheckTsCons.
      * apply CheckVar. reflexivity.
      * apply CheckTsNil.
  - apply CheckIdentP with
      (tys := [TySet;TySet]) (t := conclP ZF.Meta.Decl.Set.Pair.Unique).
    1: reflexivity.
    apply CheckTsCons.
    + apply CheckVar. reflexivity.
    + apply CheckTsCons.
      * apply CheckVar. reflexivity.
      * apply CheckTsNil.
Qed.

(* The characterization proposition is well sorted.                             *)
Proposition Charac : CheckDeclP (Pair.env) Pair.Charac.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  assert (CheckT (Pair.env) (ctxP Pair.Charac)
    (conclP Pair.Charac) TyProp) as H1. {
    apply CheckAll, CheckAll, CheckAll, CheckIff.
    - apply CheckElem.
      + apply CheckVar. reflexivity.
      + apply CheckIdentT with [TySet;TySet]. 1: reflexivity.
        apply CheckTsCons.
        * apply CheckVar. reflexivity.
        * apply CheckTsCons.
          -- apply CheckVar. reflexivity.
          -- apply CheckTsNil.
    - apply CheckOr; apply CheckEqual; apply CheckVar; reflexivity. }
  split. 1: assumption. apply CheckHoleP. assumption.
Qed.

(* The left membership proposition is well sorted.                              *)
Proposition IsInL : CheckDeclP (Pair.env) Pair.IsInL.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  assert (CheckT (Pair.env) (ctxP Pair.IsInL)
    (conclP Pair.IsInL) TyProp) as H1. {
    apply CheckAll, CheckAll, CheckElem.
    - apply CheckVar. reflexivity.
    - apply CheckIdentT with [TySet;TySet]. 1: reflexivity.
      apply CheckTsCons.
      + apply CheckVar. reflexivity.
      + apply CheckTsCons.
        * apply CheckVar. reflexivity.
        * apply CheckTsNil. }
  split. 1: assumption. apply CheckHoleP. assumption.
Qed.

(* The right membership proposition is well sorted.                             *)
Proposition IsInR : CheckDeclP (Pair.env) Pair.IsInR.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  assert (CheckT (Pair.env) (ctxP Pair.IsInR)
    (conclP Pair.IsInR) TyProp) as H1. {
    apply CheckAll, CheckAll, CheckElem.
    - apply CheckVar. reflexivity.
    - apply CheckIdentT with [TySet;TySet]. 1: reflexivity.
      apply CheckTsCons.
      + apply CheckVar. reflexivity.
      + apply CheckTsCons.
        * apply CheckVar. reflexivity.
        * apply CheckTsNil. }
  split. 1: assumption. apply CheckHoleP. assumption.
Qed.

(* The class-inclusion proposition is well sorted.                              *)
Proposition ToClassIncl : CheckDeclP (Pair.env) Pair.ToClassIncl.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  assert (CheckT (Pair.env) (ctxP Pair.ToClassIncl)
    (conclP Pair.ToClassIncl) TyProp) as H1. {
    apply CheckAll, CheckAll, CheckIff.
    - apply CheckAnd.
      + apply CheckApp.
        * apply CheckVar. reflexivity.
        * apply CheckVar. reflexivity.
      + apply CheckApp.
        * apply CheckVar. reflexivity.
        * apply CheckVar. reflexivity.
    - apply CheckIdentT with [TyClass;TyClass]. 1: reflexivity.
      apply CheckTsCons.
      + apply CheckIdentT with [TySet]. 1: reflexivity.
        apply CheckTsCons.
        * apply CheckIdentT with [TySet;TySet]. 1: reflexivity.
          apply CheckTsCons.
          -- apply CheckVar. reflexivity.
          -- apply CheckTsCons.
             ++ apply CheckVar. reflexivity.
             ++ apply CheckTsNil.
        * apply CheckTsNil.
      + apply CheckTsCons.
        * apply CheckVar. reflexivity.
        * apply CheckTsNil. }
  split. 1: assumption. apply CheckHoleP. assumption.
Qed.
