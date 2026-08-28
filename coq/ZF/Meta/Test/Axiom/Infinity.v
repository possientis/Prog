Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

Require Import ZF.Meta.Ctx.
Require Import ZF.Meta.Term.Decl.
Require Import ZF.Meta.Env.
Require Import ZF.Meta.Term.Syntax.
Require Import ZF.Meta.Term.HasTy.
Require Import ZF.Meta.HasTyIn.
Require Import ZF.Meta.Ty.

Import ListNotations.

Definition empty : Decl :=
  {| para := [];
     res  := TySet;
     body := None |}.

Definition single : Decl :=
  {| para := [TySet];
     res  := TySet;
     body := None |}.

Definition union2 : Decl :=
  {| para := [TySet; TySet];
     res  := TySet;
     body := None |}.

Definition env : Env := fun name =>
  if String.eqb name "empty"  then Some empty else
  if String.eqb name "single" then Some single else
  if String.eqb name "union2" then Some union2 else
  None.

(* exists a, empty :< a /\ forall x, x :< a -> union2 x (single x) :< a         *)
Definition Infinity : Term :=
  Ex VarTySet
    (And
      (Elem (Ident "empty" []) (Var 0))
      (All VarTySet
        (Imp
          (Elem (Var 0) (Var 1))
          (Elem
            (Ident "union2" [Var 0; Ident "single" [Var 0]])
            (Var 1))))).

(* The infinity example is a proposition in the local test environment.         *)
Proposition HasTy : HasTyIn env Ctx.empty Infinity TyProp.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  apply HasTyEx, HasTyAnd.
  - apply HasTyElem.
    + apply HasTyIdent with (argTys := []). 1: reflexivity.
      apply HasTysNil.
    + apply (HasTyVar _ _ _ TySet). reflexivity.
  - apply HasTyAll, HasTyImp.
    + apply HasTyElem; apply (HasTyVar _ _ _ TySet); reflexivity.
    + apply HasTyElem.
      * apply HasTyIdent with (argTys := [TySet; TySet]). 1: reflexivity.
        apply HasTysCons.
        -- apply (HasTyVar _ _ _ TySet). reflexivity.
        -- apply HasTysCons.
           ++ apply HasTyIdent with (argTys := [TySet]). 1: reflexivity.
              apply HasTysCons.
              ** apply (HasTyVar _ _ _ TySet). reflexivity.
              ** apply HasTysNil.
           ++ apply HasTysNil.
      * apply (HasTyVar _ _ _ TySet). reflexivity.
Qed.
