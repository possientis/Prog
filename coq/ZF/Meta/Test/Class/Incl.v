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

(* Definition Incl (P Q:Class) : Prop := forall x, P x -> Q x.                  *)
Definition Incl : Decl :=
  {| para := [TyClass; TyClass];
     res  := TyProp;
     body := Some
       (All VarTySet
         (Imp
           (App (Var 2) (Var 0))
           (App (Var 1) (Var 0)))) |}.

(* Environment.                                                                 *)

Definition env : Env := fun name =>
  if String.eqb name "toClass" then Some toClass else
  if String.eqb name "equiv"   then Some equiv else
  if String.eqb name "Incl"    then Some Incl else
  None.

(* Propositions.                                                                *)

(* Proposition Double : forall P Q, equiv P Q <-> Incl P Q /\ Incl Q P.         *)
Definition Double : Term :=
  All VarTyClass
    (All VarTyClass
      (Iff
        (Ident "equiv" [Var 1; Var 0])
        (And
          (Ident "Incl" [Var 1; Var 0])
          (Ident "Incl" [Var 0; Var 1])))).

(* Proposition EquivCompat : forall P Q R S,                                    *)
(* equiv P Q -> equiv R S -> Incl P R -> Incl Q S.                              *)
Definition EquivCompat : Term :=
  All VarTyClass
    (All VarTyClass
      (All VarTyClass
        (All VarTyClass
          (Imp
            (Ident "equiv" [Var 3; Var 2])
            (Imp
              (Ident "equiv" [Var 1; Var 0])
              (Imp
                (Ident "Incl" [Var 3; Var 1])
                (Ident "Incl" [Var 2; Var 0]))))))).

(* Proposition EquivCompatL : forall P Q R,                                     *)
(* equiv P Q -> Incl P R -> Incl Q R.                                           *)
Definition EquivCompatL : Term :=
  All VarTyClass
    (All VarTyClass
      (All VarTyClass
        (Imp
          (Ident "equiv" [Var 2; Var 1])
          (Imp
            (Ident "Incl" [Var 2; Var 0])
            (Ident "Incl" [Var 1; Var 0]))))).

(* Proposition EquivCompatR : forall P Q R,                                     *)
(* equiv P Q -> Incl R P -> Incl R Q.                                           *)
Definition EquivCompatR : Term :=
  All VarTyClass
    (All VarTyClass
      (All VarTyClass
        (Imp
          (Ident "equiv" [Var 2; Var 1])
          (Imp
            (Ident "Incl" [Var 0; Var 2])
            (Ident "Incl" [Var 0; Var 1]))))).

(* Proposition Refl : forall (P:Class), Incl P P.                               *)
Definition Refl : Term :=
  All VarTyClass
    (Ident "Incl" [Var 0; Var 0]).

(* Proposition Anti : forall P Q, Incl P Q -> Incl Q P -> equiv P Q.            *)
Definition Anti : Term :=
  All VarTyClass
    (All VarTyClass
      (Imp
        (Ident "Incl" [Var 1; Var 0])
        (Imp
          (Ident "Incl" [Var 0; Var 1])
          (Ident "equiv" [Var 1; Var 0])))).

(* Proposition Tran : forall P Q R, Incl P Q -> Incl Q R -> Incl P R.           *)
Definition Tran : Term :=
  All VarTyClass
    (All VarTyClass
      (All VarTyClass
        (Imp
          (Ident "Incl" [Var 2; Var 1])
          (Imp
            (Ident "Incl" [Var 1; Var 0])
            (Ident "Incl" [Var 2; Var 0]))))).

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

(* The declaration body for inclusion compares two classes pointwise.           *)
Proposition InclHasTyDecl : HasTyDecl Env.empty Incl.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  apply HasTyAll, HasTyImp.
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

(* The identifier toClass sends any set variable to a class.                    *)
Proposition toClassVarHasTy : forall (G:Ctx) (n:nat),
  typeOf G n = Some TySet ->
  HasTyIn env G (Ident "toClass" [Var n]) TyClass.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros G n H1.
  apply HasTyIdent with (argTys := [TySet]). 1: reflexivity.
  apply HasTysCons.
  - apply HasTyVar. assumption.
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

(* The identifier Incl sends two class arguments to a proposition.              *)
Proposition InclHasTy :
  HasTyIn env [TyClass; TyClass]
    (Ident "Incl" [Var 1; Var 0]) TyProp.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  apply HasTyIdent with (argTys := [TyClass; TyClass]). 1: reflexivity.
  apply HasTysCons.
  - apply (HasTyVar _ _ _ TyClass). reflexivity.
  - apply HasTysCons.
    + apply (HasTyVar _ _ _ TyClass). reflexivity.
    + apply HasTysNil.
Qed.

(* Inclusion applied to two class variables is well sorted.                     *)
Proposition InclVarsHasTy : forall (G:Ctx) (m n:nat),
  typeOf G m = Some TyClass ->
  typeOf G n = Some TyClass ->
  HasTyIn env G (Ident "Incl" [Var m; Var n]) TyProp.
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

(* Double inclusion and equivalence form a well-sorted proposition.             *)
Proposition DoubleHasTy : HasTyIn env Ctx.empty Double TyProp.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  apply HasTyAll, HasTyAll, HasTyIff.
  - apply equivVarsHasTy; reflexivity.
  - apply HasTyAnd; apply InclVarsHasTy; reflexivity.
Qed.

(* Compatibility of inclusion with equivalence is well sorted.                  *)
Proposition EquivCompatHasTy : HasTyIn env Ctx.empty EquivCompat TyProp.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  apply HasTyAll, HasTyAll, HasTyAll, HasTyAll, HasTyImp.
  - apply equivVarsHasTy; reflexivity.
  - apply HasTyImp.
    + apply equivVarsHasTy; reflexivity.
    + apply HasTyImp.
      * apply InclVarsHasTy; reflexivity.
      * apply InclVarsHasTy; reflexivity.
Qed.

(* Left compatibility of inclusion with equivalence is well sorted.             *)
Proposition EquivCompatLHasTy : HasTyIn env Ctx.empty EquivCompatL TyProp.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  apply HasTyAll, HasTyAll, HasTyAll, HasTyImp.
  - apply equivVarsHasTy; reflexivity.
  - apply HasTyImp; apply InclVarsHasTy; reflexivity.
Qed.

(* Right compatibility of inclusion with equivalence is well sorted.            *)
Proposition EquivCompatRHasTy : HasTyIn env Ctx.empty EquivCompatR TyProp.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  apply HasTyAll, HasTyAll, HasTyAll, HasTyImp.
  - apply equivVarsHasTy; reflexivity.
  - apply HasTyImp; apply InclVarsHasTy; reflexivity.
Qed.

(* Reflexivity of inclusion is a well-sorted proposition.                       *)
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

(* Antisymmetry of inclusion is a well-sorted proposition.                      *)
Proposition AntiHasTy : HasTyIn env Ctx.empty Anti TyProp.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  apply HasTyAll, HasTyAll, HasTyImp.
  - apply InclVarsHasTy; reflexivity.
  - apply HasTyImp.
    + apply InclVarsHasTy; reflexivity.
    + apply equivVarsHasTy; reflexivity.
Qed.

(* Transitivity of inclusion is a well-sorted proposition.                      *)
Proposition TranHasTy : HasTyIn env Ctx.empty Tran TyProp.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  apply HasTyAll, HasTyAll, HasTyAll, HasTyImp.
  - apply InclVarsHasTy; reflexivity.
  - apply HasTyImp; apply InclVarsHasTy; reflexivity.
Qed.
