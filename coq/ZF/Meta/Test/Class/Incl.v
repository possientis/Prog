Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

Require Import ZF.Meta.Check.
Require Import ZF.Meta.Proof.CheckDecl.
Require Import ZF.Meta.Proof.Decl.
Require Import ZF.Meta.Syntax.
Require Import ZF.Meta.Term.CheckDecl.
Require Import ZF.Meta.Ty.

Require Import ZF.Meta.Decl.Class.Incl.

Import ListNotations.
Open Scope string_scope.

(* Declaration typing.                                                          *)

(* The declaration body for inclusion compares two classes pointwise.           *)
Proposition Incl : CheckDeclT (Incl.env) Incl.Incl.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  apply CheckAll, CheckImp.
  - apply CheckApp.
    + apply CheckVar. reflexivity.
    + apply CheckVar. reflexivity.
  - apply CheckApp.
    + apply CheckVar. reflexivity.
    + apply CheckVar. reflexivity.
Qed.

(* Proposition typing.                                                          *)

(* Double inclusion and equivalence form a well-sorted proposition.             *)
Proposition Double : CheckDeclP (Incl.env) Incl.Double.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  assert (CheckT (Incl.env) (ctxP Incl.Double)
    (conclP Incl.Double) TyProp) as H1. {
    apply CheckIff.
    - apply CheckIdentT with [TyClass;TyClass]. 1: reflexivity.
      apply CheckTsCons.
      + apply CheckVar. reflexivity.
      + apply CheckTsCons.
        * apply CheckVar. reflexivity.
        * apply CheckTsNil.
    - apply CheckAnd.
      + apply CheckIdentT with [TyClass;TyClass]. 1: reflexivity.
        apply CheckTsCons.
        * apply CheckVar. reflexivity.
        * apply CheckTsCons.
          -- apply CheckVar. reflexivity.
          -- apply CheckTsNil.
      + apply CheckIdentT with [TyClass;TyClass]. 1: reflexivity.
        apply CheckTsCons.
        * apply CheckVar. reflexivity.
        * apply CheckTsCons.
          -- apply CheckVar. reflexivity.
          -- apply CheckTsNil. }
  split. 1: assumption. apply CheckHoleP. assumption.
Qed.

(* Compatibility of inclusion with equivalence is well sorted.                  *)
Proposition EquivCompat : CheckDeclP (Incl.env) Incl.EquivCompat.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  assert (CheckT (Incl.env) (ctxP Incl.EquivCompat)
    (conclP Incl.EquivCompat) TyProp) as H1. {
    apply CheckImp.
    - apply CheckIdentT with [TyClass;TyClass]. 1: reflexivity.
      apply CheckTsCons.
      + apply CheckVar. reflexivity.
      + apply CheckTsCons.
        * apply CheckVar. reflexivity.
        * apply CheckTsNil.
    - apply CheckImp.
      + apply CheckIdentT with [TyClass;TyClass]. 1: reflexivity.
        apply CheckTsCons.
        * apply CheckVar. reflexivity.
        * apply CheckTsCons.
          -- apply CheckVar. reflexivity.
          -- apply CheckTsNil.
      + apply CheckImp.
        * apply CheckIdentT with [TyClass;TyClass]. 1: reflexivity.
          apply CheckTsCons.
          -- apply CheckVar. reflexivity.
          -- apply CheckTsCons.
             ++ apply CheckVar. reflexivity.
             ++ apply CheckTsNil.
        * apply CheckIdentT with [TyClass;TyClass]. 1: reflexivity.
          apply CheckTsCons.
          -- apply CheckVar. reflexivity.
          -- apply CheckTsCons.
             ++ apply CheckVar. reflexivity.
             ++ apply CheckTsNil. }
  split. 1: assumption. apply CheckHoleP. assumption.
Qed.

(* Left compatibility of inclusion with equivalence is well sorted.             *)
Proposition EquivCompatL : CheckDeclP (Incl.env) Incl.EquivCompatL.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  assert (CheckT (Incl.env) (ctxP Incl.EquivCompatL)
    (conclP Incl.EquivCompatL) TyProp) as H1. {
    apply CheckImp.
    - apply CheckIdentT with [TyClass;TyClass]. 1: reflexivity.
      apply CheckTsCons.
      + apply CheckVar. reflexivity.
      + apply CheckTsCons.
        * apply CheckVar. reflexivity.
        * apply CheckTsNil.
    - apply CheckImp.
      + apply CheckIdentT with [TyClass;TyClass]. 1: reflexivity.
        apply CheckTsCons.
        * apply CheckVar. reflexivity.
        * apply CheckTsCons.
          -- apply CheckVar. reflexivity.
          -- apply CheckTsNil.
      + apply CheckIdentT with [TyClass;TyClass]. 1: reflexivity.
        apply CheckTsCons.
        * apply CheckVar. reflexivity.
        * apply CheckTsCons.
          -- apply CheckVar. reflexivity.
          -- apply CheckTsNil. }
  split. 1: assumption. apply CheckHoleP. assumption.
Qed.

(* Right compatibility of inclusion with equivalence is well sorted.            *)
Proposition EquivCompatR : CheckDeclP (Incl.env) Incl.EquivCompatR.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  assert (CheckT (Incl.env) (ctxP Incl.EquivCompatR)
    (conclP Incl.EquivCompatR) TyProp) as H1. {
    apply CheckImp.
    - apply CheckIdentT with [TyClass;TyClass]. 1: reflexivity.
      apply CheckTsCons.
      + apply CheckVar. reflexivity.
      + apply CheckTsCons.
        * apply CheckVar. reflexivity.
        * apply CheckTsNil.
    - apply CheckImp.
      + apply CheckIdentT with [TyClass;TyClass]. 1: reflexivity.
        apply CheckTsCons.
        * apply CheckVar. reflexivity.
        * apply CheckTsCons.
          -- apply CheckVar. reflexivity.
          -- apply CheckTsNil.
      + apply CheckIdentT with [TyClass;TyClass]. 1: reflexivity.
        apply CheckTsCons.
        * apply CheckVar. reflexivity.
        * apply CheckTsCons.
          -- apply CheckVar. reflexivity.
          -- apply CheckTsNil. }
  split. 1: assumption. apply CheckHoleP. assumption.
Qed.

(* Reflexivity of inclusion is a well-sorted proposition.                       *)
Proposition Refl : CheckDeclP (Incl.env) Incl.Refl.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  assert (CheckT (Incl.env) (ctxP Incl.Refl) (conclP Incl.Refl) TyProp) as H1. {
    apply CheckIdentT with [TyClass;TyClass]. 1: reflexivity.
    apply CheckTsCons.
    - apply CheckVar. reflexivity.
    - apply CheckTsCons.
      + apply CheckVar. reflexivity.
      + apply CheckTsNil. }
  split. 1: assumption. apply CheckHoleP. assumption.
Qed.

(* Antisymmetry of inclusion is a well-sorted proposition.                      *)
Proposition Anti : CheckDeclP (Incl.env) Incl.Anti.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  assert (CheckT (Incl.env) (ctxP Incl.Anti) (conclP Incl.Anti) TyProp) as H1. {
    apply CheckImp.
    - apply CheckIdentT with [TyClass;TyClass]. 1: reflexivity.
      apply CheckTsCons.
      + apply CheckVar. reflexivity.
      + apply CheckTsCons.
        * apply CheckVar. reflexivity.
        * apply CheckTsNil.
    - apply CheckImp.
      + apply CheckIdentT with [TyClass;TyClass]. 1: reflexivity.
        apply CheckTsCons.
        * apply CheckVar. reflexivity.
        * apply CheckTsCons.
          -- apply CheckVar. reflexivity.
          -- apply CheckTsNil.
      + apply CheckIdentT with [TyClass;TyClass]. 1: reflexivity.
        apply CheckTsCons.
        * apply CheckVar. reflexivity.
        * apply CheckTsCons.
          -- apply CheckVar. reflexivity.
          -- apply CheckTsNil. }
  split. 1: assumption. apply CheckHoleP. assumption.
Qed.

(* Transitivity of inclusion is a well-sorted proposition.                      *)
Proposition Tran : CheckDeclP (Incl.env) Incl.Tran.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  assert (CheckT (Incl.env) (ctxP Incl.Tran) (conclP Incl.Tran) TyProp) as H1. {
    apply CheckImp.
    - apply CheckIdentT with [TyClass;TyClass]. 1: reflexivity.
      apply CheckTsCons.
      + apply CheckVar. reflexivity.
      + apply CheckTsCons.
        * apply CheckVar. reflexivity.
        * apply CheckTsNil.
    - apply CheckImp.
      + apply CheckIdentT with [TyClass;TyClass]. 1: reflexivity.
        apply CheckTsCons.
        * apply CheckVar. reflexivity.
        * apply CheckTsCons.
          -- apply CheckVar. reflexivity.
          -- apply CheckTsNil.
      + apply CheckIdentT with [TyClass;TyClass]. 1: reflexivity.
        apply CheckTsCons.
        * apply CheckVar. reflexivity.
        * apply CheckTsCons.
          -- apply CheckVar. reflexivity.
          -- apply CheckTsNil. }
  split. 1: assumption. apply CheckHoleP. assumption.
Qed.
