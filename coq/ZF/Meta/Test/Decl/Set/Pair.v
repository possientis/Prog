Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

Require Import ZF.Meta.Ctx.
Require Import ZF.Meta.Env.
Require Import ZF.Meta.Proof.Decl.
Require Import ZF.Meta.Syntax.
Require Import ZF.Meta.Term.Decl.
Require Import ZF.Meta.Term.HasTyDecl.
Require Import ZF.Meta.Term.HasTy.
Require Import ZF.Meta.Ty.

Import ListNotations.

(* Declarations.                                                                *)

(* Definition IsPairOf (a b:U) : Class := fun x =>                              *)
(* forall y, y :< x <-> y = a \/ y = b.                                         *)
Definition IsPairOf : DeclT :=
  mkDeclT [TySet; TySet] TyClass (Some
       (Lam
         (All VarTySet
           (Iff
             (Elem (Var 0) (Var 1))
             (Or
               (Equal (Var 0) (Var 3))
               (Equal (Var 0) (Var 2))))))).

(* The existence proof declaration states that some set is a pair of a and b.   *)
Definition pairExists : DeclP :=
  mkDeclP [TySet; TySet]
      (Ex VarTySet
         (App
           (IdentT "IsPairOf" [Var 2; Var 1])
           (Var 0))) None.

(* The uniqueness proof declaration states that any two such sets are equal.    *)
Definition pairUnique : DeclP :=
  mkDeclP [TySet; TySet]
      (All VarTySet
         (All VarTySet
           (Imp
             (App
               (IdentT "IsPairOf" [Var 3; Var 2])
               (Var 1))
             (Imp
               (App
                 (IdentT "IsPairOf" [Var 3; Var 2])
                 (Var 0))
               (Equal (Var 1) (Var 0)))))) None.

(* Definition pair (a b:U) : U := Def (IsPairOf a b) exists unique.             *)
Definition pair : DeclT :=
  mkDeclT [TySet; TySet] TySet (Some
       (Def
         (IdentT "IsPairOf" [Var 1; Var 0])
         (IdentP "pairExists" [Var 1; Var 0])
         (IdentP "pairUnique" [Var 1; Var 0]))).

(* Environment.                                                                 *)

Definition env : Env := Env.unions
  [ Env.fromListT
      [ ("IsPairOf"%string  , IsPairOf)
      ; ("pair"%string      , pair)
      ]
  ; Env.fromListP
      [ ("pairExists"%string, pairExists)
      ; ("pairUnique"%string, pairUnique)
      ]
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

(* The existence proof declaration conclusion is a well-sorted proposition.     *)
Proposition pairExistsCheckConcl :
  HasTy env (ctxP pairExists) (conclP pairExists) TyProp.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  apply HasTyEx, HasTyApp.
  - apply HasTyIdentT with [TySet; TySet]. 1: reflexivity.
    apply HasTysCons.
    + apply (HasTyVar _ _ _ TySet). reflexivity.
    + apply HasTysCons.
      * apply (HasTyVar _ _ _ TySet). reflexivity.
      * apply HasTysNil.
  - apply (HasTyVar _ _ _ TySet). reflexivity.
Qed.

(* The uniqueness proof declaration conclusion is a well-sorted proposition.    *)
Proposition pairUniqueCheckConcl :
  HasTy env (ctxP pairUnique) (conclP pairUnique) TyProp.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  apply HasTyAll, HasTyAll, HasTyImp.
  - apply HasTyApp.
    + apply HasTyIdentT with [TySet; TySet]. 1: reflexivity.
      apply HasTysCons.
      * apply (HasTyVar _ _ _ TySet). reflexivity.
      * apply HasTysCons.
        -- apply (HasTyVar _ _ _ TySet). reflexivity.
        -- apply HasTysNil.
    + apply (HasTyVar _ _ _ TySet). reflexivity.
  - apply HasTyImp.
    + apply HasTyApp.
      * apply HasTyIdentT with [TySet; TySet]. 1: reflexivity.
        apply HasTysCons.
        -- apply (HasTyVar _ _ _ TySet). reflexivity.
        -- apply HasTysCons.
           ++ apply (HasTyVar _ _ _ TySet). reflexivity.
           ++ apply HasTysNil.
      * apply (HasTyVar _ _ _ TySet). reflexivity.
    + apply HasTyEqual; apply (HasTyVar _ _ _ TySet); reflexivity.
Qed.

(* The declaration body for pair denotes a set backed by proof references.      *)
Proposition pairCheckBody : HasTyDecl env pair.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  apply HasTyDef.
  - apply HasTyIdentT with [TySet; TySet]. 1: reflexivity.
    apply HasTysCons.
    + apply (HasTyVar _ _ _ TySet). reflexivity.
    + apply HasTysCons.
      * apply (HasTyVar _ _ _ TySet). reflexivity.
      * apply HasTysNil.
  - apply HasTyIdentP with pairExists. 1: reflexivity.
    + apply HasTysCons.
      * apply (HasTyVar _ _ _ TySet). reflexivity.
      * apply HasTysCons.
        -- apply (HasTyVar _ _ _ TySet). reflexivity.
        -- apply HasTysNil.
    + apply pairExistsCheckConcl.
  - apply HasTyIdentP with pairUnique. 1: reflexivity.
    + apply HasTysCons.
      * apply (HasTyVar _ _ _ TySet). reflexivity.
      * apply HasTysCons.
        -- apply (HasTyVar _ _ _ TySet). reflexivity.
        -- apply HasTysNil.
    + apply pairUniqueCheckConcl.
Qed.

(* Identifier checks.                                                           *)

(* IsPairOf applied to two set variables is well sorted anywhere.               *)
Proposition IsPairOfCheckIdent : forall (e:Env) (G:Ctx) (m n:nat),
  e "IsPairOf"%string = Some IsPairOf ->
  typeOf G m = Some TySet ->
  typeOf G n = Some TySet ->
  HasTy e G (IdentT "IsPairOf" [Var m; Var n]) TyClass.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros e G m n H1 H2 H3.
  apply HasTyIdentT with [TySet; TySet].
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
  HasTy e G (IdentT "pair" [Var m; Var n]) TySet.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros e G m n H1 H2 H3.
  apply HasTyIdentT with [TySet; TySet].
  - unfold Env.toSigs. rewrite H1. reflexivity.
  - apply HasTysCons.
    + apply HasTyVar. assumption.
    + apply HasTysCons.
      * apply HasTyVar. assumption.
      * apply HasTysNil.
Qed.
