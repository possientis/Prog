Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

Require Import ZF.Meta.Ctx.
Require Import ZF.Meta.Sig.
Require Import ZF.Meta.Term.
Require Import ZF.Meta.Ty.

Import ListNotations.

Definition sig : Sig := fun name =>
  if String.eqb name "empty" then Some ([]              , TySet) else
  if String.eqb name "inter" then Some ([TySet; TySet]  , TySet) else
  None.

(* forall a, a <> empty -> exists x, x :< a /\ inter x a = empty                *)
Definition Foundation : Term :=
  All VarTySet
    (Imp
      (NotEq (Var 0) (Ident "empty" []))
      (Ex VarTySet
        (And
          (Elem (Var 0) (Var 1))
          (Equal
            (Ident "inter" [Var 0; Var 1])
            (Ident "empty" []))))).

(* The foundation example is a proposition in the local test signature.         *)
Proposition HasTy : HasTy sig Ctx.empty Foundation TyProp.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  apply HasTyAll, HasTyImp.
  - apply HasTyNotEq.
    + apply (HasTyVar _ _ _ TySet). reflexivity.
    + apply HasTyIdent with (argTys := []). 1: reflexivity.
      apply HasTysNil.
  - apply HasTyEx, HasTyAnd.
    + apply HasTyElem; apply (HasTyVar _ _ _ TySet); reflexivity.
    + apply HasTyEqual.
      * apply HasTyIdent with (argTys := [TySet; TySet]). 1: reflexivity.
        apply HasTysCons.
        -- apply (HasTyVar _ _ _ TySet). reflexivity.
        -- apply HasTysCons.
           ++ apply (HasTyVar _ _ _ TySet). reflexivity.
           ++ apply HasTysNil.
      * apply HasTyIdent with (argTys := []). 1: reflexivity.
        apply HasTysNil.
Qed.
