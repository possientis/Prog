Require Import Coq.Lists.List.

Require Import ZF.Meta.Check.Core.
Require Import ZF.Meta.Check.DeclP.
Require Import ZF.Meta.Check.DeclT.
Require Import ZF.Meta.Apply.
Require Import ZF.Meta.DeclP.
Require Import ZF.Meta.DeclT.
Require Import ZF.Meta.Env.
Require Import ZF.Meta.Exists.
Require Import ZF.Meta.Shift.
Require Import ZF.Meta.Small.
Require Import ZF.Meta.Subst.
Require Import ZF.Meta.SyntaxT.
Require Import ZF.Meta.SyntaxP.
Require Import ZF.Meta.Ty.
Require Import ZF.Meta.Unique.

Import ListNotations.

(* A tactic for routine syntax-directed checker obligations.                    *)
Ltac check :=
  match goal with
  | |- Core.CheckT _ _ Bot         TyProp   => apply CheckBot
  | |- Core.CheckT _ _ Top         TyProp   => apply CheckTop
  | |- Core.CheckT _ _ (Var _) _            => apply CheckVar; reflexivity
  | |- Core.CheckT _ _ (HoleT _) _          => apply CheckHoleT
  | |- Core.CheckT ?E _ (IdentT ?name _) _  =>
      let s := eval cbv in (sigT E name) in
      lazymatch s with
      | Some (?tys, ?ty) =>
          let tys' := constr:(tys) in
          let ty'  := constr:(ty) in
          eapply (CheckIdentT _ _ name _ tys' ty'); [reflexivity|check]
      | None => fail 100 "unknown term declaration" name
      end
  | |- Core.CheckT _ _ (Elem _ _)  TyProp   => apply CheckElem; check
  | |- Core.CheckT _ _ (Leq _ _)   TyProp   => apply CheckLeq; check
  | |- Core.CheckT _ _ (Geq _ _)   TyProp   => apply CheckGeq; check
  | |- Core.CheckT _ _ (Lt _ _)    TyProp   => apply CheckLt; check
  | |- Core.CheckT _ _ (Gt _ _)    TyProp   => apply CheckGt; check
  | |- Core.CheckT _ _ (Equal _ _) TyProp   => apply CheckEqual; check
  | |- Core.CheckT _ _ (NotEq _ _) TyProp   => apply CheckNotEq; check
  | |- Core.CheckT _ _ (Imp _ _)   TyProp   => apply CheckImp; check
  | |- Core.CheckT _ _ (Iff _ _)   TyProp   => apply CheckIff; check
  | |- Core.CheckT _ _ (And _ _)   TyProp   => apply CheckAnd; check
  | |- Core.CheckT _ _ (Or _ _)    TyProp   => apply CheckOr; check
  | |- Core.CheckT _ _ (Not _)     TyProp   => apply CheckNot; check
  | |- Core.CheckT _ _ (All _)     TyProp   => apply CheckAll; check
  | |- Core.CheckT _ _ (Ex _)      TyProp   => apply CheckEx; check
  | |- Core.CheckT _ _ (Lam _)     TyClass  => apply CheckLam; check
  | |- Core.CheckT _ _ (App _ _)   TyProp   => apply CheckApp; check
  | |- Core.CheckT _ _ (Def _) TySet      => apply CheckDef; check
  | |- Core.CheckT _ _ (FromC _) TySet    => apply CheckFromC; check
  | |- Core.CheckT _ _ _ _                  =>
      tryif progress (cbv [Exists Unique Small shiftT])
      then check
      else fail 1 "unsupported term-checking goal"
  | |- Core.CheckTs _ _ NilT []             => apply CheckTsNil
  | |- Core.CheckTs _ _ (ConsT _ _) (_ :: _)=> apply CheckTsCons; check
  | |- Core.CheckTs _ _ NilT _              => cbn; apply CheckTsNil
  | |- Core.CheckTs _ _ (ConsT _ _) _       => cbn; apply CheckTsCons; check
  | |- Core.CheckP _ _ (HoleP _) _          => apply CheckHoleP; check
  | |- Core.CheckP _ _ (AxiomP _) _         => apply CheckAxiomP; check
  | |- Core.CheckP ?E ?G (IdentP ?name ?args) _ =>
      tryif
        progress
          (cbv [Exists Unique Small applyT argT substT Subst.fromT Subst.fromTs
                Shift.shiftT Shift.fromT nthT revT appT lengthT toList];
          cbn)
      then
        check
      else
        let s := eval cbv in (sigP E name) in
        lazymatch s with
        | Some (?tys, ?t) =>
            let tys' := constr:(tys) in
            let t' := constr:(t) in
            change (Core.CheckP E G (IdentP name args) (applyT t' args));
            eapply (CheckIdentP _ _ name args tys' t'); [reflexivity|check]
        | None => fail 100 "unknown proof declaration" name
        end
      end.

Ltac checkT :=
  cbv [DeclT.CheckT args fromList ctxT paraT resT bodyT];
  check.

Ltac checkP :=
  cbv [DeclP.CheckP args fromList ctxP conclP paraP bodyP];
  split; check.
