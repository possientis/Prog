Require Import ZF.Meta.Ctx.
Require Import ZF.Meta.Env.
Require Import ZF.Meta.Syntax.
Require Import ZF.Meta.Term.HasTy.
Require Import ZF.Meta.Ty.

(* forall P, forall a, exists b, forall x, x :< b <-> x :< a /\ P x             *)
Definition Specification : Term :=
  All VarTyClass
    (All VarTySet
      (Ex VarTySet
        (All VarTySet
          (Iff
            (Elem (Var 0) (Var 1))
            (And
              (Elem (Var 0) (Var 2))
              (App (Var 3) (Var 0))))))).

(* The specification example is a proposition in the empty environment.         *)
Proposition HasTy : HasTy Env.empty Ctx.empty Specification TyProp.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  apply HasTyAll, HasTyAll, HasTyEx, HasTyAll, HasTyIff.
  - apply HasTyElem; apply (HasTyVar _ _ _ TySet); reflexivity.
  - apply HasTyAnd.
    + apply HasTyElem; apply (HasTyVar _ _ _ TySet); reflexivity.
    + apply HasTyApp.
      * apply (HasTyVar _ _ _ TyClass). reflexivity.
      * apply (HasTyVar _ _ _ TySet). reflexivity.
Qed.
