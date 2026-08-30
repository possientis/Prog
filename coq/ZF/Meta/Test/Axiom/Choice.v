Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

Require Import ZF.Meta.HasTy.
Require Import ZF.Meta.Term.HasTyDecl.
Require Import ZF.Meta.Syntax.
Require Import ZF.Meta.Ty.

Import ListNotations.

Require Import ZF.Meta.Decl.Axiom.Choice.

Proposition Choice : HasTyDeclT (Choice.env) Choice.
Proof.
  apply HasTyAll, HasTyEx, HasTyAnd.
  - apply HasTyIdentT with [TySet;TySet]. 1: reflexivity.
    apply HasTyTsCons.
    + apply (HasTyVar _ _ _ TySet). reflexivity.
    + apply HasTyTsCons.
      * apply (HasTyVar _ _ _ TySet). reflexivity.
      * apply HasTyTsNil.
  - apply HasTyAll, HasTyImp.
    + apply HasTyElem; apply (HasTyVar _ _ _ TySet); reflexivity.
    + apply HasTyImp.
      * apply HasTyNotEq.
        -- apply (HasTyVar _ _ _ TySet). reflexivity.
        -- apply HasTyIdentT with []. 1: reflexivity.
           apply HasTyTsNil.
      * apply HasTyElem.
        -- apply HasTyIdentT with [TySet;TySet]. 1: reflexivity.
           apply HasTyTsCons.
           ++ apply (HasTyVar _ _ _ TySet). reflexivity.
           ++ apply HasTyTsCons.
              ** apply (HasTyVar _ _ _ TySet). reflexivity.
              ** apply HasTyTsNil.
        -- apply (HasTyVar _ _ _ TySet). reflexivity.
Qed.
