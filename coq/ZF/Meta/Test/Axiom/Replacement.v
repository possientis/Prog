Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

Require Import ZF.Meta.Ctx.
Require Import ZF.Meta.Term.Decl.
Require Import ZF.Meta.Env.
Require Import ZF.Meta.Syntax.
Require Import ZF.Meta.HasTy.
Require Import ZF.Meta.Ty.

Import ListNotations.

Definition Functional : Decl :=
  {| para := [TyClass];
     res  := TyProp;
     body := None |}.

Definition ordPair : Decl :=
  {| para := [TySet; TySet];
     res  := TySet;
     body := None |}.

Definition env : Env := Env.fromListT
  [ ("Functional"%string, Functional)
  ; ("ordPair"%string  , ordPair)
  ].

(* forall F, Functional F ->                                                    *)
(* forall a, exists b, forall y, y :< b <-> exists x, x :< a /\ F :(x,y):       *)
Definition Replacement : Term :=
  All VarTyClass
    (Imp
      (IdentT "Functional" [Var 0])
      (All VarTySet
        (Ex VarTySet
          (All VarTySet
            (Iff
              (Elem (Var 0) (Var 1))
              (Ex VarTySet
                (And
                  (Elem (Var 0) (Var 3))
                  (App
                    (Var 4)
                    (IdentT "ordPair" [Var 0; Var 1]))))))))).

(* The replacement example is a proposition in the local test environment.      *)
Proposition HasTy : HasTyT env Ctx.empty Replacement TyProp.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  apply HasTyAll, HasTyImp.
  - apply HasTyIdentT with (d:=Functional). 1: reflexivity.
    apply HasTyTsCons.
    + apply (HasTyVar _ _ _ TyClass). reflexivity.
    + apply HasTyTsNil.
  - apply HasTyAll, HasTyEx, HasTyAll, HasTyIff.
    + apply HasTyElem; apply (HasTyVar _ _ _ TySet); reflexivity.
    + apply HasTyEx, HasTyAnd.
      * apply HasTyElem; apply (HasTyVar _ _ _ TySet); reflexivity.
      * apply HasTyApp.
        -- apply (HasTyVar _ _ _ TyClass). reflexivity.
        -- apply HasTyIdentT with (d:=ordPair). 1: reflexivity.
           apply HasTyTsCons.
           ++ apply (HasTyVar _ _ _ TySet). reflexivity.
           ++ apply HasTyTsCons.
              ** apply (HasTyVar _ _ _ TySet). reflexivity.
              ** apply HasTyTsNil.
Qed.
