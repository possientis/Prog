Require Import ZF.Meta.Ctx.
Require Import ZF.Meta.Env.
Require Import ZF.Meta.Syntax.
Require Import ZF.Meta.Check.
Require Import ZF.Meta.Ty.

(* forall a, exists b, forall x, x :< b <-> x <= a                              *)
Definition Power : Term :=
  All VarTySet
    (Ex VarTySet
      (All VarTySet
        (Iff
          (Elem (Var 0) (Var 1))
          (Leq (Var 0) (Var 2))))).

(* The power example is a proposition in the empty environment.                 *)
Proposition Check : CheckT Env.empty Ctx.empty Power TyProp.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  apply CheckAll, CheckEx, CheckAll, CheckIff.
  - apply CheckElem; apply (CheckVar _ _ _ TySet); reflexivity.
  - apply CheckLeq; apply (CheckVar _ _ _ TySet); reflexivity.
Qed.
