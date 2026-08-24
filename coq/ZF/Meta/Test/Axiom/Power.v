Require Import ZF.Meta.Ctx.
Require Import ZF.Meta.Sig.
Require Import ZF.Meta.Term.
Require Import ZF.Meta.Ty.

(* Source: forall a, exists b, forall x, x :< b <-> x <= a.                     *)
Definition Power : Term :=
  All VarTySet
    (Ex VarTySet
      (All VarTySet
        (Iff
          (Elem (Var 0) (Var 1))
          (Leq (Var 0) (Var 2))))).

(* The power example is a proposition in the empty environment.                 *)
Proposition HasTy : HasTy Sig.empty Ctx.empty Power TyProp.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  apply HasTyAll, HasTyEx, HasTyAll, HasTyIff.
  - apply HasTyElem; apply (HasTyVar _ _ _ VarTySet); reflexivity.
  - apply HasTyLeq; apply (HasTyVar _ _ _ VarTySet); reflexivity.
Qed.
