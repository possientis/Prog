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

(* Definition toClass (a:U) : Class := fun x => x :< a.                         *)
Definition toClass : Decl :=
  {| paraT := [TySet];
     resT  := TyClass;
     bodyT := Lam (Elem (Var 0) (Var 1)) |}.

(* Definition equiv (P Q:Class) : Prop := forall x, P x <-> Q x.                *)
Definition equiv : Decl :=
  {| paraT := [TyClass; TyClass];
     resT  := TyProp;
     bodyT :=
       (All VarTySet
         (Iff
           (App (Var 2) (Var 0))
           (App (Var 1) (Var 0)))) |}.

(* Environment.                                                                 *)

Definition imports : Env := Env.empty.

Definition exports : Env := Env.fromListT
  [ ("toClass"%string, toClass)
  ; ("equiv"%string  , equiv)
  ].

Definition env : Env := Env.union imports exports.

(* Body checks.                                                                 *)

(* The declaration body for toClass maps a set to its membership class.         *)
Proposition toClassCheckBody : CheckDecl Env.empty toClass.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  apply CheckLam, CheckElem; apply CheckVar; reflexivity.
Qed.

(* The declaration body for equivalence compares two classes pointwise.         *)
Proposition equivCheckBody : CheckDecl Env.empty equiv.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  apply CheckAll, CheckIff.
  - apply CheckApp.
    + apply CheckVar. reflexivity.
    + apply CheckVar. reflexivity.
  - apply CheckApp.
    + apply CheckVar. reflexivity.
    + apply CheckVar. reflexivity.
Qed.

(* Identifier checks.                                                           *)

(* The identifier toClass sends any set variable to a class in any environment. *)
Proposition toClassCheckIdent : forall (e:Env) (G:Ctx) (n:nat),
  Env.sigT e "toClass"%string = Some ([TySet], TyClass) ->
  typeOf G n = Some TySet ->
  CheckT e G (IdentT "toClass" [Var n]) TyClass.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros e G n H1 H2.
  apply CheckIdentT with [TySet]. 1: assumption.
  - apply CheckTsCons.
    + apply CheckVar. assumption.
    + apply CheckTsNil.
Qed.

(* Equivalence applied to two class variables is well sorted anywhere.          *)
Proposition equivCheckIdent : forall (e:Env) (G:Ctx) (m n:nat),
  Env.sigT e "equiv"%string = Some ([TyClass; TyClass], TyProp) ->
  typeOf G m = Some TyClass ->
  typeOf G n = Some TyClass ->
  CheckT e G (IdentT "equiv" [Var m; Var n]) TyProp.
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

(* Negated equivalence of two class variables is well sorted anywhere.          *)
Proposition notEquivCheckIdent : forall (e:Env) (G:Ctx) (m n:nat),
  Env.sigT e "equiv"%string = Some ([TyClass; TyClass], TyProp) ->
  typeOf G m = Some TyClass ->
  typeOf G n = Some TyClass ->
  CheckT e G (Not (IdentT "equiv" [Var m; Var n])) TyProp.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros e G m n H1 H2 H3.
  apply CheckNot.
  apply equivCheckIdent; assumption.
Qed.
