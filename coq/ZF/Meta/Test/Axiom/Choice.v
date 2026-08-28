Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

Require Import ZF.Meta.Ctx.
Require Import ZF.Meta.DeclTerm.
Require Import ZF.Meta.Env.
Require Import ZF.Meta.Term.
Require Import ZF.Meta.HasTy.
Require Import ZF.Meta.HasTyIn.
Require Import ZF.Meta.Ty.

Import ListNotations.

Definition FunctionOn : DeclTerm :=
  {| para := [TySet; TySet];
     res  := TyProp;
     body := None |}.

Definition empty : DeclTerm :=
  {| para := [];
     res  := TySet;
     body := None |}.

Definition eval : DeclTerm :=
  {| para := [TySet; TySet];
     res  := TySet;
     body := None |}.

Definition env : Env := fun name =>
  if String.eqb name "FunctionOn" then Some FunctionOn else
  if String.eqb name "empty"      then Some empty else
  if String.eqb name "eval"       then Some eval else
  None.

(* forall a,                                                                    *)
(*  exists f, FunctionOn f a /\ forall x, x :< a -> x <> empty -> eval f x :< x *)
Definition Choice : Term :=
  All VarTySet
    (Ex VarTySet
      (And
        (Ident "FunctionOn" [Var 0; Var 1])
        (All VarTySet
          (Imp
            (Elem (Var 0) (Var 2))
            (Imp
              (NotEq (Var 0) (Ident "empty" []))
              (Elem (Ident "eval" [Var 1; Var 0]) (Var 0))))))).

(* The choice example is a proposition in the local test environment.           *)
Proposition HasTy : HasTyIn env Ctx.empty Choice TyProp.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  apply HasTyAll, HasTyEx, HasTyAnd.
  - apply HasTyIdent with (argTys := [TySet; TySet]). 1: reflexivity.
    apply HasTysCons.
    + apply (HasTyVar _ _ _ TySet). reflexivity.
    + apply HasTysCons.
      * apply (HasTyVar _ _ _ TySet). reflexivity.
      * apply HasTysNil.
  - apply HasTyAll, HasTyImp.
    + apply HasTyElem; apply (HasTyVar _ _ _ TySet); reflexivity.
    + apply HasTyImp.
      * apply HasTyNotEq.
        -- apply (HasTyVar _ _ _ TySet). reflexivity.
        -- apply HasTyIdent with (argTys := []). 1: reflexivity.
           apply HasTysNil.
      * apply HasTyElem.
        -- apply HasTyIdent with (argTys := [TySet; TySet]). 1: reflexivity.
           apply HasTysCons.
           ++ apply (HasTyVar _ _ _ TySet). reflexivity.
           ++ apply HasTysCons.
              ** apply (HasTyVar _ _ _ TySet). reflexivity.
              ** apply HasTysNil.
        -- apply (HasTyVar _ _ _ TySet). reflexivity.
Qed.
