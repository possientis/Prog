Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

Require Import ZF.Meta.Ctx.
Require Import ZF.Meta.Decl.
Require Import ZF.Meta.Env.
Require Import ZF.Meta.HasTyDecl.
Require Import ZF.Meta.HasTy.
Require Import ZF.Meta.HasTyIn.
Require Import ZF.Meta.Term.
Require Import ZF.Meta.Ty.

Import ListNotations.

Definition toClass : Decl :=
  {| para := [TySet];
     res  := TyClass;
     body := Some (Lam (Elem (Var 0) (Var 1))) |}.

Definition env : Env := fun name =>
  if String.eqb name "toClass" then Some toClass else
  None.

(* The declaration body for toClass maps a set to its membership class.         *)
Proposition toClassHasTyDecl : HasTyDecl Env.empty toClass.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  apply HasTyLam, HasTyElem; apply (HasTyVar _ _ _ TySet); reflexivity.
Qed.

(* The identifier toClass sends a set argument to a class.                      *)
Proposition toClassHasTy :
  HasTyIn env [TySet] (Ident "toClass" [Var 0]) TyClass.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  apply HasTyIdent with (argTys := [TySet]). 1: reflexivity.
  apply HasTysCons.
  - apply (HasTyVar _ _ _ TySet). reflexivity.
  - apply HasTysNil.
Qed.
