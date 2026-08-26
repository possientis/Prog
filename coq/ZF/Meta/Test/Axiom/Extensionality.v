Require Import ZF.Meta.Ctx.
Require Import ZF.Meta.Sig.
Require Import ZF.Meta.Term.
Require Import ZF.Meta.HasTy.
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
Proposition HasTy : HasTy Sig.empty Ctx.empty Extensionality TyProp.
Proof.
  apply HasTyAll, HasTyAll, HasTyImp.
  - apply HasTyAll, HasTyIff.
    + apply HasTyElem; apply (HasTyVar _ _ _ TySet); reflexivity.
    + apply HasTyElem; apply (HasTyVar _ _ _ TySet); reflexivity.
  - apply HasTyEqual;  apply (HasTyVar _ _ _ TySet); reflexivity.
Qed.
