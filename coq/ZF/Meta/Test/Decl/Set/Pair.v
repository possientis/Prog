Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

Require Import ZF.Meta.Ctx.
Require Import ZF.Meta.Term.Decl.
Require Import ZF.Meta.Env.
Require Import ZF.Meta.Term.HasTyDecl.
Require Import ZF.Meta.Term.HasTy.
Require Import ZF.Meta.Term.Syntax.
Require Import ZF.Meta.Ty.

Import ListNotations.

(* Declarations.                                                                *)

(* Definition IsPairOf (a b:U) : Class := fun x =>                              *)
(* forall y, y :< x <-> y = a \/ y = b.                                         *)
Definition IsPairOf : Decl :=
  {| para := [TySet; TySet];
     res  := TyClass;
     body := Some
       (Lam
         (All VarTySet
           (Iff
             (Elem (Var 0) (Var 1))
             (Or
               (Equal (Var 0) (Var 3))
               (Equal (Var 0) (Var 2)))))) |}.

(* Definition pair (a b:U) : U := The (IsPairOf a b).                           *)
Definition pair : Decl :=
  {| para := [TySet; TySet];
     res  := TySet;
     body := Some
       (The
         (App
           (Ident "IsPairOf" [Var 2; Var 1])
           (Var 0))) |}.

(* Environment.                                                                 *)

Definition env : Env := Env.fromListT
  [ ("IsPairOf"%string, IsPairOf)
  ; ("pair"%string    , pair)
  ].

(* Body checks.                                                                 *)

(* The declaration body for IsPairOf recognizes the two selected sets.          *)
Proposition IsPairOfCheckBody : HasTyDecl Env.empty IsPairOf.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  apply HasTyLam, HasTyAll, HasTyIff.
  - apply HasTyElem; apply (HasTyVar _ _ _ TySet); reflexivity.
  - apply HasTyOr; apply HasTyEqual; apply (HasTyVar _ _ _ TySet); reflexivity.
Qed.

(* The declaration body for pair denotes the set satisfying IsPairOf.           *)
Proposition pairCheckBody : HasTyDecl env pair.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  apply HasTyThe, HasTyApp.
  - apply HasTyIdent with [TySet; TySet]. 1: reflexivity.
    apply HasTysCons.
    + apply (HasTyVar _ _ _ TySet). reflexivity.
    + apply HasTysCons.
      * apply (HasTyVar _ _ _ TySet). reflexivity.
      * apply HasTysNil.
  - apply (HasTyVar _ _ _ TySet). reflexivity.
Qed.

(* Identifier checks.                                                           *)

(* IsPairOf applied to two set variables is well sorted anywhere.               *)
Proposition IsPairOfCheckIdent : forall (e:Env) (G:Ctx) (m n:nat),
  e "IsPairOf"%string = Some IsPairOf ->
  typeOf G m = Some TySet ->
  typeOf G n = Some TySet ->
  HasTy e G (Ident "IsPairOf" [Var m; Var n]) TyClass.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros e G m n H1 H2 H3.
  apply HasTyIdent with [TySet; TySet].
  - unfold Env.toSigs. rewrite H1. reflexivity.
  - apply HasTysCons.
    + apply HasTyVar. assumption.
    + apply HasTysCons.
      * apply HasTyVar. assumption.
      * apply HasTysNil.
Qed.

(* Pair applied to two set variables is well sorted anywhere.                   *)
Proposition pairCheckIdent : forall (e:Env) (G:Ctx) (m n:nat),
  e "pair"%string = Some pair ->
  typeOf G m = Some TySet ->
  typeOf G n = Some TySet ->
  HasTy e G (Ident "pair" [Var m; Var n]) TySet.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros e G m n H1 H2 H3.
  apply HasTyIdent with [TySet; TySet].
  - unfold Env.toSigs. rewrite H1. reflexivity.
  - apply HasTysCons.
    + apply HasTyVar. assumption.
    + apply HasTysCons.
      * apply HasTyVar. assumption.
      * apply HasTysNil.
Qed.
