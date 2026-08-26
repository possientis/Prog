Require Import ZF.Meta.Ctx.
Require Import ZF.Meta.Env.
Require Import ZF.Meta.Term.
Require Import ZF.Meta.HasTy.
Require Import ZF.Meta.HasTyIn.
Require Import ZF.Meta.Ty.

(* forall a b, exists c, forall x, x :< c <-> x = a \/ x = b                    *)
Definition Pairing : Term :=
  All VarTySet
    (All VarTySet
      (Ex VarTySet
        (All VarTySet
          (Iff
            (Elem (Var 0) (Var 1))
            (Or
              (Equal (Var 0) (Var 3))
              (Equal (Var 0) (Var 2))))))).

(* The pairing example is a proposition in the empty environment.               *)
Proposition HasTy : HasTyIn Env.empty Ctx.empty Pairing TyProp.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  apply HasTyAll, HasTyAll, HasTyEx, HasTyAll, HasTyIff.
  - apply HasTyElem; apply (HasTyVar _ _ _ TySet); reflexivity.
  - apply HasTyOr.
    + apply HasTyEqual; apply (HasTyVar _ _ _ TySet); reflexivity.
    + apply HasTyEqual; apply (HasTyVar _ _ _ TySet); reflexivity.
Qed.
