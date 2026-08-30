Require Import ZF.Meta.Ctx.
Require Import ZF.Meta.Env.
Require Import ZF.Meta.Syntax.
Require Import ZF.Meta.Check.
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
Proposition Check : CheckT Env.empty Ctx.empty Specification TyProp.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  apply CheckAll, CheckAll, CheckEx, CheckAll, CheckIff.
  - apply CheckElem; apply CheckVar; reflexivity.
  - apply CheckAnd.
    + apply CheckElem; apply CheckVar; reflexivity.
    + apply CheckApp.
      * apply CheckVar. reflexivity.
      * apply CheckVar. reflexivity.
Qed.
