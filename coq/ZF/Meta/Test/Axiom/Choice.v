Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

Require Import ZF.Meta.Ctx.
Require Import ZF.Meta.Term.Decl.
Require Import ZF.Meta.Env.
Require Import ZF.Meta.Syntax.
Require Import ZF.Meta.HasTy.
Require Import ZF.Meta.Ty.

Import ListNotations.

Definition FunctionOn : Decl :=
  {| para := [TySet; TySet];
     res  := TyProp;
     body := None |}.

Definition empty : Decl :=
  {| para := [];
     res  := TySet;
     body := None |}.

Definition eval : Decl :=
  {| para := [TySet; TySet];
     res  := TySet;
     body := None |}.

Definition env : Env := Env.fromListT
  [ ("FunctionOn"%string, FunctionOn)
  ; ("empty"%string     , empty)
  ; ("eval"%string      , eval)
  ].

(* forall a,                                                                    *)
(*  exists f, FunctionOn f a /\ forall x, x :< a -> x <> empty -> eval f x :< x *)
Definition Choice : Term :=
  All VarTySet
    (Ex VarTySet
      (And
        (IdentT "FunctionOn" [Var 0; Var 1])
        (All VarTySet
          (Imp
            (Elem (Var 0) (Var 2))
            (Imp
              (NotEq (Var 0) (IdentT "empty" []))
              (Elem (IdentT "eval" [Var 1; Var 0]) (Var 0))))))).

(* The choice example is a proposition in the local test environment.           *)
Proposition HasTy : HasTyT env Ctx.empty Choice TyProp.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  apply HasTyAll, HasTyEx, HasTyAnd.
  - apply HasTyIdentT with [TySet; TySet]. 1: reflexivity.
    apply HasTyTsCons.
    + apply (HasTyVar _ _ _ TySet). reflexivity.
    + apply HasTyTsCons.
      * apply (HasTyVar _ _ _ TySet). reflexivity.
      * apply HasTyTsNil.
  - apply HasTyAll, HasTyImp.
    + apply HasTyElem; apply (HasTyVar _ _ _ TySet); reflexivity.
    + apply HasTyImp.
      * apply HasTyNotEq.
        -- apply (HasTyVar _ _ _ TySet). reflexivity.
        -- apply HasTyIdentT with []. 1: reflexivity.
           apply HasTyTsNil.
      * apply HasTyElem.
        -- apply HasTyIdentT with [TySet; TySet]. 1: reflexivity.
           apply HasTyTsCons.
           ++ apply (HasTyVar _ _ _ TySet). reflexivity.
           ++ apply HasTyTsCons.
              ** apply (HasTyVar _ _ _ TySet). reflexivity.
              ** apply HasTyTsNil.
        -- apply (HasTyVar _ _ _ TySet). reflexivity.
Qed.
