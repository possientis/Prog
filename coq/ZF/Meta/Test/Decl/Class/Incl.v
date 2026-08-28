Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

Require Import ZF.Meta.Ctx.
Require Import ZF.Meta.Term.Decl.
Require Import ZF.Meta.Env.
Require Import ZF.Meta.Term.HasTyDecl.
Require Import ZF.Meta.Term.HasTy.
Require Import ZF.Meta.HasTyIn.
Require Import ZF.Meta.Term.Syntax.
Require Import ZF.Meta.Ty.

Import ListNotations.

(* Declarations.                                                                *)

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

Definition env : Env := Env.fromListT [("Incl"%string, Incl)].

(* Body checks.                                                                 *)

(* The declaration body for inclusion compares two classes pointwise.           *)
Proposition InclCheckBody : HasTyDecl Env.empty Incl.
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

(* Identifier checks.                                                           *)

(* Inclusion applied to two class variables is well sorted anywhere.            *)
Proposition InclCheckIdent : forall (e:Env) (G:Ctx) (m n:nat),
  e "Incl"%string = Some Incl ->
  typeOf G m = Some TyClass ->
  typeOf G n = Some TyClass ->
  HasTyIn e G (Ident "Incl" [Var m; Var n]) TyProp.
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
