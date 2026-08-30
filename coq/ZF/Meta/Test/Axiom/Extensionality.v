Require Import ZF.Meta.Ctx.
Require Import ZF.Meta.Env.
Require Import ZF.Meta.Syntax.
Require Import ZF.Meta.Check.
Require Import ZF.Meta.Ty.

(* forall a b, (forall x, x :< a <-> x :< b) -> a = b                           *)
Definition Extensionality : Term :=
  All VarTySet
    (All VarTySet
      (Imp
        (All VarTySet
          (Iff (Elem (Var 0) (Var 2))
               (Elem (Var 0) (Var 1))))
        (Equal (Var 1) (Var 0)))).

(* The extensionality example is a proposition in the empty environment.        *)
Proposition ExtensionalityCheck :
  CheckT Env.empty Ctx.empty Extensionality TyProp.
Proof.
  apply CheckAll, CheckAll, CheckImp.
  - apply CheckAll, CheckIff.
    + apply CheckElem; apply CheckVar; reflexivity.
    + apply CheckElem; apply CheckVar; reflexivity.
  - apply CheckEqual;  apply CheckVar; reflexivity.
Qed.
