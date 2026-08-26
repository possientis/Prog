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

(* Propositions.                                                                *)

(* Proposition Refl : forall (P:Class), equiv P P.                              *)
Definition Refl : Term :=
  All VarTyClass
    (Ident "equiv" [Var 0; Var 0]).

(* Proposition EquivCompat : forall A B C D,                                    *)
(* equiv A C -> equiv B D -> equiv A B -> equiv C D.                            *)
Definition EquivCompat : Term :=
  All VarTyClass
    (All VarTyClass
      (All VarTyClass
        (All VarTyClass
          (Imp
            (Ident "equiv" [Var 3; Var 1])
            (Imp
              (Ident "equiv" [Var 2; Var 0])
              (Imp
                (Ident "equiv" [Var 3; Var 2])
                (Ident "equiv" [Var 1; Var 0]))))))).

(* Proposition EquivCompatL : forall A B C,                                     *)
(* equiv A C -> equiv A B -> equiv C B.                                         *)
Definition EquivCompatL : Term :=
  All VarTyClass
    (All VarTyClass
      (All VarTyClass
        (Imp
          (Ident "equiv" [Var 2; Var 0])
          (Imp
            (Ident "equiv" [Var 2; Var 1])
            (Ident "equiv" [Var 0; Var 1]))))).

(* Proposition EquivCompatR : forall A B C,                                     *)
(* equiv B C -> equiv A B -> equiv A C.                                         *)
Definition EquivCompatR : Term :=
  All VarTyClass
    (All VarTyClass
      (All VarTyClass
        (Imp
          (Ident "equiv" [Var 1; Var 0])
          (Imp
            (Ident "equiv" [Var 2; Var 1])
            (Ident "equiv" [Var 2; Var 0]))))).

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

(* Equivalence applied to two class variables is well sorted.                   *)
Proposition equivVarsHasTy : forall (G:Ctx) (m n:nat),
  typeOf G m = Some TyClass ->
  typeOf G n = Some TyClass ->
  HasTyIn env G (Ident "equiv" [Var m; Var n]) TyProp.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros G m n H1 H2.
  apply HasTyIdent with (argTys := [TyClass; TyClass]). 1: reflexivity.
  apply HasTysCons.
  - apply HasTyVar. assumption.
  - apply HasTysCons.
    + apply HasTyVar. assumption.
    + apply HasTysNil.
Qed.

(* Proposition typing.                                                          *)

(* The reflexivity proposition is well sorted using equivalence.                *)
Proposition ReflHasTy : HasTyIn env Ctx.empty Refl TyProp.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  apply HasTyAll.
  apply HasTyIdent with (argTys := [TyClass; TyClass]). 1: reflexivity.
  apply HasTysCons.
  - apply (HasTyVar _ _ _ TyClass). reflexivity.
  - apply HasTysCons.
    + apply (HasTyVar _ _ _ TyClass). reflexivity.
    + apply HasTysNil.
Qed.

(* Equivalence compatibility is a well-sorted proposition.                      *)
Proposition EquivCompatHasTy : HasTyIn env Ctx.empty EquivCompat TyProp.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  apply HasTyAll, HasTyAll, HasTyAll, HasTyAll, HasTyImp.
  - apply equivVarsHasTy; reflexivity.
  - apply HasTyImp.
    + apply equivVarsHasTy; reflexivity.
    + apply HasTyImp.
      * apply equivVarsHasTy; reflexivity.
      * apply equivVarsHasTy; reflexivity.
Qed.

(* Left compatibility of equivalence is a well-sorted proposition.              *)
Proposition EquivCompatLHasTy : HasTyIn env Ctx.empty EquivCompatL TyProp.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  apply HasTyAll, HasTyAll, HasTyAll, HasTyImp.
  - apply equivVarsHasTy; reflexivity.
  - apply HasTyImp; apply equivVarsHasTy; reflexivity.
Qed.

(* Right compatibility of equivalence is a well-sorted proposition.             *)
Proposition EquivCompatRHasTy : HasTyIn env Ctx.empty EquivCompatR TyProp.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  apply HasTyAll, HasTyAll, HasTyAll, HasTyImp.
  - apply equivVarsHasTy; reflexivity.
  - apply HasTyImp; apply equivVarsHasTy; reflexivity.
Qed.
