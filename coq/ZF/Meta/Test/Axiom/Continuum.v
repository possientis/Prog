Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

Require Import ZF.Meta.Check.
Require Import ZF.Meta.Proof.CheckDecl.
Require Import ZF.Meta.Term.CheckDecl.
Require Import ZF.Meta.Syntax.
Require Import ZF.Meta.Ty.

Import ListNotations.
Open Scope string_scope.

Require Import ZF.Meta.Decl.Axiom.Continuum.

Proposition CH : CheckDeclT (Continuum.env) CH.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  apply CheckEqual.
  - apply CheckIdentT with [TySet]. 1: reflexivity.
    apply CheckTsCons.
    + apply CheckIdentT with [TySet]. 1: reflexivity.
      apply CheckTsCons.
      * apply CheckIdentT with []. 1: reflexivity.
        apply CheckTsNil.
      * apply CheckTsNil.
    + apply CheckTsNil.
  - apply CheckIdentT with [TyClass;TySet]. 1: reflexivity.
    apply CheckTsCons.
    + apply CheckIdentT with []. 1: reflexivity.
      apply CheckTsNil.
    + apply CheckTsCons.
      * apply CheckIdentT with []. 1: reflexivity.
        apply CheckTsNil.
      * apply CheckTsNil.
Qed.

Proposition GCH : CheckDeclT (Continuum.env) GCH.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  apply CheckAll, CheckImp.
  - apply CheckIdentT with [TySet]. 1: reflexivity.
    apply CheckTsCons.
    + apply CheckVar. reflexivity.
    + apply CheckTsNil.
  - apply CheckEqual.
    + apply CheckIdentT with [TySet]. 1: reflexivity.
      apply CheckTsCons.
      * apply CheckIdentT with [TySet]. 1: reflexivity.
        apply CheckTsCons.
        -- apply CheckIdentT with [TyClass;TySet]. 1: reflexivity.
           apply CheckTsCons.
           ++ apply CheckIdentT with []. 1: reflexivity.
              apply CheckTsNil.
           ++ apply CheckTsCons.
              ** apply CheckVar. reflexivity.
              ** apply CheckTsNil.
        -- apply CheckTsNil.
      * apply CheckTsNil.
    + apply CheckIdentT with [TyClass;TySet]. 1: reflexivity.
      apply CheckTsCons.
      * apply CheckIdentT with []. 1: reflexivity.
        apply CheckTsNil.
      * apply CheckTsCons.
        -- apply CheckIdentT with [TySet]. 1: reflexivity.
           apply CheckTsCons.
           ++ apply CheckVar. reflexivity.
           ++ apply CheckTsNil.
        -- apply CheckTsNil.
Qed.

Proposition WhenGCH : CheckDeclP (Continuum.env) WhenGCH.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  split.
  - apply CheckImp.
    + apply CheckIdentT with []. 1: reflexivity.
      apply CheckTsNil.
    + apply CheckIdentT with []. 1: reflexivity.
      apply CheckTsNil.
  - apply CheckHoleP.
    apply CheckImp.
    + apply CheckIdentT with []. 1: reflexivity.
      apply CheckTsNil.
    + apply CheckIdentT with []. 1: reflexivity.
      apply CheckTsNil.
Qed.
