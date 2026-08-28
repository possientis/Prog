Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

Require Import ZF.Meta.Ctx.
Require Import ZF.Meta.Term.Decl.
Require Import ZF.Meta.Env.
Require Import ZF.Meta.Syntax.
Require Import ZF.Meta.HasTy.
Require Import ZF.Meta.Ty.

Import ListNotations.

Definition empty : Decl :=
  {| para := [];
     res  := TySet;
     body := None |}.

Definition inter : Decl :=
  {| para := [TySet; TySet];
     res  := TySet;
     body := None |}.

Definition env : Env := Env.fromListT
  [ ("empty"%string, empty)
  ; ("inter"%string, inter)
  ].

(* forall a, a <> empty -> exists x, x :< a /\ inter x a = empty                *)
Definition Foundation : Term :=
  All VarTySet
    (Imp
      (NotEq (Var 0) (IdentT "empty" []))
      (Ex VarTySet
        (And
          (Elem (Var 0) (Var 1))
          (Equal
            (IdentT "inter" [Var 0; Var 1])
            (IdentT "empty" []))))).

(* The foundation example is a proposition in the local test environment.       *)
Proposition HasTy : HasTyT env Ctx.empty Foundation TyProp.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  apply HasTyAll, HasTyImp.
  - apply HasTyNotEq.
    + apply (HasTyVar _ _ _ TySet). reflexivity.
    + apply HasTyIdentT with (d:=empty). 1: reflexivity.
      apply HasTyTsNil.
  - apply HasTyEx, HasTyAnd.
    + apply HasTyElem; apply (HasTyVar _ _ _ TySet); reflexivity.
    + apply HasTyEqual.
      * apply HasTyIdentT with (d:=inter). 1: reflexivity.
        apply HasTyTsCons.
        -- apply (HasTyVar _ _ _ TySet). reflexivity.
        -- apply HasTyTsCons.
           ++ apply (HasTyVar _ _ _ TySet). reflexivity.
           ++ apply HasTyTsNil.
      * apply HasTyIdentT with (d:=empty). 1: reflexivity.
        apply HasTyTsNil.
Qed.
