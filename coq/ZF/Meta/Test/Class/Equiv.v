Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

Require Import ZF.Meta.Check.
Require Import ZF.Meta.Proof.CheckDecl.
Require Import ZF.Meta.Proof.Decl.
Require Import ZF.Meta.Syntax.
Require Import ZF.Meta.Term.CheckDecl.
Require Import ZF.Meta.Ty.

Require Import ZF.Meta.Decl.Class.Equiv.

Import ListNotations.

(* Declaration typing.                                                          *)

(* The declaration body for toClass maps a set to its membership class.         *)
Proposition toClass : CheckDeclT (Equiv.env) toClass.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  apply CheckLam, CheckElem; apply CheckVar; reflexivity.
Qed.

(* The declaration body for equivalence compares two classes pointwise.         *)
Proposition equiv : CheckDeclT (Equiv.env) equiv.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  apply CheckAll, CheckIff.
  - apply CheckApp.
    + apply CheckVar. reflexivity.
    + apply CheckVar. reflexivity.
  - apply CheckApp.
    + apply CheckVar. reflexivity.
    + apply CheckVar. reflexivity.
Qed.

(* Proposition typing.                                                          *)

(* The reflexivity proposition is well sorted using equivalence.                *)
Proposition Refl : CheckDeclP (Equiv.env) Refl.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  assert (CheckT (Equiv.env) (ctxP Refl) (conclP Refl) TyProp) as H1. {
    apply CheckAll.
    apply CheckIdentT with [TyClass;TyClass]. 1: reflexivity.
    apply CheckTsCons.
    + apply CheckVar. reflexivity.
    + apply CheckTsCons.
      * apply CheckVar. reflexivity.
      * apply CheckTsNil. }
  split. 1: assumption. apply CheckHoleP. assumption.
Qed.

(* Equivalence compatibility is a well-sorted proposition.                      *)
Proposition EquivCompat : CheckDeclP (Equiv.env) EquivCompat.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  assert (CheckT (Equiv.env) (ctxP EquivCompat)
    (conclP EquivCompat) TyProp) as H1. {
    apply CheckAll, CheckAll, CheckAll, CheckAll, CheckImp.
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
      * apply CheckImp.
        -- apply CheckIdentT with [TyClass;TyClass]. 1: reflexivity.
          apply CheckTsCons.
          ++ apply CheckVar. reflexivity.
          ++ apply CheckTsCons.
             ** apply CheckVar. reflexivity.
             ** apply CheckTsNil.
        -- apply CheckIdentT with [TyClass;TyClass]. 1: reflexivity.
          apply CheckTsCons.
          ++ apply CheckVar. reflexivity.
          ++ apply CheckTsCons.
             ** apply CheckVar. reflexivity.
             ** apply CheckTsNil. }
  split. 1: assumption. apply CheckHoleP. assumption.
Qed.

(* Left compatibility of equivalence is a well-sorted proposition.              *)
Proposition EquivCompatL : CheckDeclP (Equiv.env) EquivCompatL.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  assert (CheckT (Equiv.env) (ctxP EquivCompatL)
    (conclP EquivCompatL) TyProp) as H1. {
    apply CheckAll, CheckAll, CheckAll, CheckImp.
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

(* Right compatibility of equivalence is a well-sorted proposition.             *)
Proposition EquivCompatR : CheckDeclP (Equiv.env) EquivCompatR.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  assert (CheckT (Equiv.env) (ctxP EquivCompatR)
    (conclP EquivCompatR) TyProp) as H1. {
    apply CheckAll, CheckAll, CheckAll, CheckImp.
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

(* Symmetry of equivalence is a well-sorted proposition.                        *)
Proposition Sym : CheckDeclP (Equiv.env) Sym.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  assert (CheckT (Equiv.env) (ctxP Sym) (conclP Sym) TyProp) as H1. {
    apply CheckAll, CheckAll, CheckImp.
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

(* Transitivity of equivalence is a well-sorted proposition.                    *)
Proposition Tran : CheckDeclP (Equiv.env) Tran.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  assert (CheckT (Equiv.env) (ctxP Tran) (conclP Tran) TyProp) as H1. {
    apply CheckAll, CheckAll, CheckAll, CheckImp.
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

(* Symmetry of non-equivalence is a well-sorted proposition.                    *)
Proposition NotSym : CheckDeclP (Equiv.env) NotSym.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  assert (CheckT (Equiv.env) (ctxP NotSym) (conclP NotSym) TyProp) as H1. {
    apply CheckAll, CheckAll, CheckImp.
    + apply CheckNot.
      apply CheckIdentT with [TyClass;TyClass]. 1: reflexivity.
      apply CheckTsCons.
      * apply CheckVar. reflexivity.
      * apply CheckTsCons.
        -- apply CheckVar. reflexivity.
        -- apply CheckTsNil.
    + apply CheckNot.
      apply CheckIdentT with [TyClass;TyClass]. 1: reflexivity.
      apply CheckTsCons.
      * apply CheckVar. reflexivity.
      * apply CheckTsCons.
        -- apply CheckVar. reflexivity.
        -- apply CheckTsNil. }
  split. 1: assumption. apply CheckHoleP. assumption.
Qed.

(* Equality of sets and equivalence of their classes is well sorted.            *)
Proposition EqualToClass : CheckDeclP (Equiv.env) EqualToClass.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  assert (CheckT (Equiv.env) (ctxP EqualToClass)
    (conclP EqualToClass) TyProp) as H1. {
    apply CheckAll, CheckAll, CheckIff.
    + apply CheckEqual; apply CheckVar; reflexivity.
    + apply CheckIdentT with [TyClass;TyClass]. 1: reflexivity.
      apply CheckTsCons.
      * apply CheckIdentT with [TySet]. 1: reflexivity.
        apply CheckTsCons.
        -- apply CheckVar. reflexivity.
        -- apply CheckTsNil.
      * apply CheckTsCons.
        -- apply CheckIdentT with [TySet]. 1: reflexivity.
          apply CheckTsCons.
          ++ apply CheckVar. reflexivity.
          ++ apply CheckTsNil.
        -- apply CheckTsNil. }
  split. 1: assumption. apply CheckHoleP. assumption.
Qed.

(* Inequality of sets and non-equivalence of their classes is well sorted.      *)
Proposition NotEqualToClass : CheckDeclP (Equiv.env) NotEqualToClass.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  assert (CheckT (Equiv.env) (ctxP NotEqualToClass)
    (conclP NotEqualToClass) TyProp) as H1. {
    apply CheckAll, CheckAll, CheckIff.
    + apply CheckNotEq; apply CheckVar; reflexivity.
    + apply CheckNot.
      apply CheckIdentT with [TyClass;TyClass]. 1: reflexivity.
      apply CheckTsCons.
      * apply CheckIdentT with [TySet]. 1: reflexivity.
        apply CheckTsCons.
        -- apply CheckVar. reflexivity.
        -- apply CheckTsNil.
      * apply CheckTsCons.
        -- apply CheckIdentT with [TySet]. 1: reflexivity.
          apply CheckTsCons.
          ++ apply CheckVar. reflexivity.
          ++ apply CheckTsNil.
        -- apply CheckTsNil. }
  split. 1: assumption. apply CheckHoleP. assumption.
Qed.

(* Non-equivalence is compatible with equivalence.                              *)
Proposition NotCompat : CheckDeclP (Equiv.env) NotCompat.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  assert (CheckT (Equiv.env) (ctxP NotCompat) (conclP NotCompat) TyProp) as H1. {
    apply CheckAll, CheckAll, CheckAll, CheckAll, CheckImp.
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
      * apply CheckImp.
        -- apply CheckNot.
          apply CheckIdentT with [TyClass;TyClass]. 1: reflexivity.
          apply CheckTsCons.
          ++ apply CheckVar. reflexivity.
          ++ apply CheckTsCons.
             ** apply CheckVar. reflexivity.
             ** apply CheckTsNil.
        -- apply CheckNot.
          apply CheckIdentT with [TyClass;TyClass]. 1: reflexivity.
          apply CheckTsCons.
          ++ apply CheckVar. reflexivity.
          ++ apply CheckTsCons.
             ** apply CheckVar. reflexivity.
             ** apply CheckTsNil. }
  split. 1: assumption. apply CheckHoleP. assumption.
Qed.

(* Non-equivalence is left-compatible with equivalence.                         *)
Proposition NotCompatL : CheckDeclP (Equiv.env) NotCompatL.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  assert (CheckT (Equiv.env) (ctxP NotCompatL)
    (conclP NotCompatL) TyProp) as H1. {
    apply CheckAll, CheckAll, CheckAll, CheckImp.
    + apply CheckIdentT with [TyClass;TyClass]. 1: reflexivity.
      apply CheckTsCons.
      * apply CheckVar. reflexivity.
      * apply CheckTsCons.
        -- apply CheckVar. reflexivity.
        -- apply CheckTsNil.
    + apply CheckImp.
      * apply CheckNot.
        apply CheckIdentT with [TyClass;TyClass]. 1: reflexivity.
        apply CheckTsCons.
        -- apply CheckVar. reflexivity.
        -- apply CheckTsCons.
          ++ apply CheckVar. reflexivity.
          ++ apply CheckTsNil.
      * apply CheckNot.
        apply CheckIdentT with [TyClass;TyClass]. 1: reflexivity.
        apply CheckTsCons.
        -- apply CheckVar. reflexivity.
        -- apply CheckTsCons.
          ++ apply CheckVar. reflexivity.
          ++ apply CheckTsNil. }
  split. 1: assumption. apply CheckHoleP. assumption.
Qed.

(* Non-equivalence is right-compatible with equivalence.                        *)
Proposition NotCompatR : CheckDeclP (Equiv.env) NotCompatR.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  assert (CheckT (Equiv.env) (ctxP NotCompatR)
  (conclP NotCompatR) TyProp) as H1. {
    apply CheckAll, CheckAll, CheckAll, CheckImp.
    + apply CheckIdentT with [TyClass;TyClass]. 1: reflexivity.
      apply CheckTsCons.
      * apply CheckVar. reflexivity.
      * apply CheckTsCons.
        -- apply CheckVar. reflexivity.
        -- apply CheckTsNil.
    + apply CheckImp.
      * apply CheckNot.
        apply CheckIdentT with [TyClass;TyClass]. 1: reflexivity.
        apply CheckTsCons.
        -- apply CheckVar. reflexivity.
        -- apply CheckTsCons.
          ++ apply CheckVar. reflexivity.
          ++ apply CheckTsNil.
      * apply CheckNot.
        apply CheckIdentT with [TyClass;TyClass]. 1: reflexivity.
        apply CheckTsCons.
        -- apply CheckVar. reflexivity.
        -- apply CheckTsCons.
          ++ apply CheckVar. reflexivity.
          ++ apply CheckTsNil. }
  split. 1: assumption. apply CheckHoleP. assumption.
Qed.
