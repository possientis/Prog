Require Import ZF.Meta.Ctx.
Require Import ZF.Meta.Env.
Require Import ZF.Meta.Syntax.
Require Import ZF.Meta.Term.HasTy.
Require Import ZF.Meta.Ty.

(* exists x, True                                                               *)
Definition NonEmptyUniverse : Term :=
  Ex VarTySet Top.

(* The non-empty-universe example is a proposition in the empty environment.    *)
Proposition HasTy : HasTy Env.empty Ctx.empty NonEmptyUniverse TyProp.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  apply HasTyEx, HasTyTop.
Qed.
