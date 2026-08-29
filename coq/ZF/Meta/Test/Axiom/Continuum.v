Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

Require Import ZF.Meta.HasTy.
Require Import ZF.Meta.Proof.HasTyDecl.
Require Import ZF.Meta.Term.HasTyDecl.
Require Import ZF.Meta.Syntax.
Require Import ZF.Meta.Ty.

Import ListNotations.

Require Import ZF.Meta.Decl.Axiom.Continuum.

Proposition CH : HasTyDeclT (Continuum.env) CH.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  apply HasTyEqual.
  - apply HasTyIdentT with (d:=card). 1: reflexivity.
    apply HasTyTsCons.
    + apply HasTyIdentT with (d:=power). 1: reflexivity.
      apply HasTyTsCons.
      * apply HasTyIdentT with (d:=omega). 1: reflexivity.
        apply HasTyTsNil.
      * apply HasTyTsNil.
    + apply HasTyTsNil.
  - apply HasTyIdentT with (d:=eval). 1: reflexivity.
    apply HasTyTsCons.
    + apply HasTyIdentT with (d:=Aleph). 1: reflexivity.
      apply HasTyTsNil.
    + apply HasTyTsCons.
      * apply HasTyIdentT with (d:=one). 1: reflexivity.
        apply HasTyTsNil.
      * apply HasTyTsNil.
Qed.

Proposition GCH : HasTyDeclT (Continuum.env) GCH.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  apply HasTyAll, HasTyImp.
  - apply HasTyIdentT with (d:=Ordinal). 1: reflexivity.
    apply HasTyTsCons.
    + apply (HasTyVar _ _ _ TySet). reflexivity.
    + apply HasTyTsNil.
  - apply HasTyEqual.
    + apply HasTyIdentT with (d:=card). 1: reflexivity.
      apply HasTyTsCons.
      * apply HasTyIdentT with (d:=power). 1: reflexivity.
        apply HasTyTsCons.
        -- apply HasTyIdentT with (d:=eval). 1: reflexivity.
           apply HasTyTsCons.
           ++ apply HasTyIdentT with (d:=Aleph). 1: reflexivity.
              apply HasTyTsNil.
           ++ apply HasTyTsCons.
              ** apply (HasTyVar _ _ _ TySet). reflexivity.
              ** apply HasTyTsNil.
        -- apply HasTyTsNil.
      * apply HasTyTsNil.
    + apply HasTyIdentT with (d:=eval). 1: reflexivity.
      apply HasTyTsCons.
      * apply HasTyIdentT with (d:=Aleph). 1: reflexivity.
        apply HasTyTsNil.
      * apply HasTyTsCons.
        -- apply HasTyIdentT with (d:=succ). 1: reflexivity.
           apply HasTyTsCons.
           ++ apply (HasTyVar _ _ _ TySet). reflexivity.
           ++ apply HasTyTsNil.
        -- apply HasTyTsNil.
Qed.

Proposition WhenGCH : HasTyDeclP (Continuum.env) WhenGCH.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  split.
  - apply HasTyImp.
    + apply HasTyIdentT with (d:=Decl.Axiom.Continuum.GCH). 1: reflexivity.
      apply HasTyTsNil.
    + apply HasTyIdentT with (d:=Decl.Axiom.Continuum.CH). 1: reflexivity.
      apply HasTyTsNil.
  - apply HasTyHoleP.
    apply HasTyImp.
    + apply HasTyIdentT with (d:=Decl.Axiom.Continuum.GCH). 1: reflexivity.
      apply HasTyTsNil.
    + apply HasTyIdentT with (d:=Decl.Axiom.Continuum.CH). 1: reflexivity.
      apply HasTyTsNil.
Qed.
