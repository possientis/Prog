Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

Require Import ZF.Meta.Ctx.
Require Import ZF.Meta.DeclTerm.
Require Import ZF.Meta.Env.
Require Import ZF.Meta.HasTyDeclTerm.
Require Import ZF.Meta.HasTy.
Require Import ZF.Meta.HasTyIn.
Require Import ZF.Meta.Term.
Require Import ZF.Meta.Ty.

Import ListNotations.

(* Declarations.                                                                *)

(* Definition toClass (a:U) : Class := fun x => x :< a.                         *)
Definition toClass : DeclTerm :=
  {| para := [TySet];
     res  := TyClass;
     body := Some (Lam (Elem (Var 0) (Var 1))) |}.

(* Definition equiv (P Q:Class) : Prop := forall x, P x <-> Q x.                *)
Definition equiv : DeclTerm :=
  {| para := [TyClass; TyClass];
     res  := TyProp;
     body := Some
       (All VarTySet
         (Iff
           (App (Var 2) (Var 0))
           (App (Var 1) (Var 0)))) |}.

(* Environment.                                                                 *)

Definition env : Env := Env.fromList
  [("toClass"%string, toClass)
  ; ("equiv"%string, equiv)].

(* Body checks.                                                                 *)

(* The declaration body for toClass maps a set to its membership class.         *)
Proposition toClassCheckBody : HasTyDeclTerm Env.empty toClass.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  apply HasTyLam, HasTyElem; apply (HasTyVar _ _ _ TySet); reflexivity.
Qed.

(* The declaration body for equivalence compares two classes pointwise.         *)
Proposition equivCheckBody : HasTyDeclTerm Env.empty equiv.
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

(* Identifier checks.                                                           *)

(* The identifier toClass sends any set variable to a class in any environment. *)
Proposition toClassCheckIdent : forall (e:Env) (G:Ctx) (n:nat),
  e "toClass"%string = Some toClass ->
  typeOf G n = Some TySet ->
  HasTyIn e G (Ident "toClass" [Var n]) TyClass.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros e G n H1 H2.
  apply HasTyIdent with (argTys := [TySet]).
  - unfold Env.toSigs. rewrite H1. reflexivity.
  - apply HasTysCons.
    + apply HasTyVar. assumption.
    + apply HasTysNil.
Qed.

(* Equivalence applied to two class variables is well sorted anywhere.          *)
Proposition equivCheckIdent : forall (e:Env) (G:Ctx) (m n:nat),
  e "equiv"%string = Some equiv ->
  typeOf G m = Some TyClass ->
  typeOf G n = Some TyClass ->
  HasTyIn e G (Ident "equiv" [Var m; Var n]) TyProp.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros e G m n H1 H2 H3.
  apply HasTyIdent with (argTys := [TyClass; TyClass]).
  - unfold Env.toSigs. rewrite H1. reflexivity.
  - apply HasTysCons.
    + apply HasTyVar. assumption.
    + apply HasTysCons.
      * apply HasTyVar. assumption.
      * apply HasTysNil.
Qed.

(* Negated equivalence of two class variables is well sorted anywhere.          *)
Proposition notEquivCheckIdent : forall (e:Env) (G:Ctx) (m n:nat),
  e "equiv"%string = Some equiv ->
  typeOf G m = Some TyClass ->
  typeOf G n = Some TyClass ->
  HasTyIn e G (Not (Ident "equiv" [Var m; Var n])) TyProp.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros e G m n H1 H2 H3.
  apply HasTyNot.
  apply equivCheckIdent; assumption.
Qed.
