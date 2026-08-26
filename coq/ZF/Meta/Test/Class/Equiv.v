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

(* Declarations.                                                                *)

(* Definition toClass (a:U) : Class := fun x => x :< a.                         *)
Definition toClass : Decl :=
  {| para := [TySet];
     res  := TyClass;
     body := Some (Lam (Elem (Var 0) (Var 1))) |}.

(* Definition equiv (P Q:Class) : Prop := forall x, P x <-> Q x.                *)
Definition equiv : Decl :=
  {| para := [TyClass; TyClass];
     res  := TyProp;
     body := Some
       (All VarTySet
         (Iff
           (App (Var 2) (Var 0))
           (App (Var 1) (Var 0)))) |}.

(* Environment.                                                                 *)

Definition env : Env := fun name =>
  if String.eqb name "toClass" then Some toClass else
  if String.eqb name "equiv"   then Some equiv else
  None.

(* Declaration typing.                                                          *)

(* The declaration body for toClass maps a set to its membership class.         *)
Proposition toClassHasTyDecl : HasTyDecl Env.empty toClass.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  apply HasTyLam, HasTyElem; apply (HasTyVar _ _ _ TySet); reflexivity.
Qed.

(* The declaration body for equivalence compares two classes pointwise.         *)
Proposition equivHasTyDecl : HasTyDecl Env.empty equiv.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  apply HasTyAll, HasTyIff.
  - apply HasTyApp.
    + apply (HasTyVar _ _ _ TyClass). reflexivity.
    + apply (HasTyVar _ _ _ TySet). reflexivity.
  - apply HasTyApp.
    + apply (HasTyVar _ _ _ TyClass). reflexivity.
    + apply (HasTyVar _ _ _ TySet). reflexivity.
Qed.

(* Identifier typing.                                                           *)

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

(* The identifier equiv sends two class arguments to a proposition.             *)
Proposition equivHasTy :
  HasTyIn env [TyClass; TyClass]
    (Ident "equiv" [Var 1; Var 0]) TyProp.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  apply HasTyIdent with (argTys := [TyClass; TyClass]). 1: reflexivity.
  apply HasTysCons.
  - apply (HasTyVar _ _ _ TyClass). reflexivity.
  - apply HasTysCons.
    + apply (HasTyVar _ _ _ TyClass). reflexivity.
    + apply HasTysNil.
Qed.
