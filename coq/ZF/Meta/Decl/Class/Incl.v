Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

Require Import ZF.Meta.Ctx.
Require Import ZF.Meta.Term.Decl.
Require Import ZF.Meta.Env.
Require Import ZF.Meta.Term.CheckDecl.
Require Import ZF.Meta.Check.
Require Import ZF.Meta.Syntax.
Require Import ZF.Meta.Ty.

Import ListNotations.

(* Declarations.                                                                *)

(* Definition Incl (P Q:Class) : Prop := forall x, P x -> Q x.                  *)
Definition Incl : Decl :=
  {| paraT := [TyClass; TyClass];
     resT  := TyProp;
     bodyT :=
       (All VarTySet
         (Imp
           (App (Var 2) (Var 0))
           (App (Var 1) (Var 0)))) |}.

(* Environment.                                                                 *)

Definition env : Env := Env.fromListT [("Incl"%string, Incl)].

(* Body checks.                                                                 *)

(* The declaration body for inclusion compares two classes pointwise.           *)
Proposition InclCheckBody : CheckDecl Env.empty Incl.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  apply CheckAll, CheckImp.
  - apply CheckApp.
    + apply (CheckVar _ _ _ TyClass). reflexivity.
    + apply (CheckVar _ _ _ TySet). reflexivity.
  - apply CheckApp.
    + apply (CheckVar _ _ _ TyClass). reflexivity.
    + apply (CheckVar _ _ _ TySet). reflexivity.
Qed.

(* Identifier checks.                                                           *)

(* Inclusion applied to two class variables is well sorted anywhere.            *)
Proposition InclCheckIdent : forall (e:Env) (G:Ctx) (m n:nat),
  Env.sigT e "Incl"%string = Some ([TyClass; TyClass], TyProp) ->
  typeOf G m = Some TyClass ->
  typeOf G n = Some TyClass ->
  CheckT e G (IdentT "Incl" [Var m; Var n]) TyProp.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros e G m n H1 H2 H3.
  apply CheckIdentT with [TyClass;TyClass]. 1: assumption.
  - apply CheckTsCons.
    + apply CheckVar. assumption.
    + apply CheckTsCons.
      * apply CheckVar. assumption.
      * apply CheckTsNil.
Qed.
