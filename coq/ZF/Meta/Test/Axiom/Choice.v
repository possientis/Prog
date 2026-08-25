Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

Require Import ZF.Meta.Ctx.
Require Import ZF.Meta.Sig.
Require Import ZF.Meta.Term.
Require Import ZF.Meta.Ty.

Import ListNotations.

Definition sig : Sig := fun name =>
  if String.eqb name "FunctionOn" then Some ([TySet; TySet], TyProp) else
  if String.eqb name "empty"      then Some ([]              , TySet ) else
  if String.eqb name "eval"       then Some ([TySet; TySet], TySet ) else
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

(* The choice example is a proposition in the local test signature.             *)
Proposition HasTy : HasTy sig Ctx.empty Choice TyProp.
Proof.
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
