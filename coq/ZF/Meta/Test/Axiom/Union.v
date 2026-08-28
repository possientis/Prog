Require Import ZF.Meta.Ctx.
Require Import ZF.Meta.Env.
Require Import ZF.Meta.Syntax.
Require Import ZF.Meta.HasTy.
Require Import ZF.Meta.Ty.

(* forall a, exists b, forall x, x :< b <-> exists y, x :< y /\ y :< a          *)
Definition Union : Term :=
  All VarTySet
    (Ex VarTySet
      (All VarTySet
        (Iff
          (Elem (Var 0) (Var 1))
          (Ex VarTySet
            (And
              (Elem (Var 1) (Var 0))
              (Elem (Var 0) (Var 3))))))).

(* The union example is a proposition in the empty environment.                 *)
Proposition HasTy : HasTyT Env.empty Ctx.empty Union TyProp.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  apply HasTyAll, HasTyEx, HasTyAll, HasTyIff.
  - apply HasTyElem; apply (HasTyVar _ _ _ TySet); reflexivity.
  - apply HasTyEx, HasTyAnd.
    + apply HasTyElem; apply (HasTyVar _ _ _ TySet); reflexivity.
    + apply HasTyElem; apply (HasTyVar _ _ _ TySet); reflexivity.
Qed.
