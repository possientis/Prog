Require Import Coq.Lists.List.

Require Import ZF.Meta.Check.CoreT.
Require Import ZF.Meta.Check.CoreP.
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
  | |- CoreT.CheckT _ _ Bot         TyProp        => apply CheckBot
  | |- CoreT.CheckT _ _ Top         TyProp        => apply CheckTop
  | |- CoreT.CheckT _ _ (Var _) _                 => apply CheckVar; reflexivity
  | |- CoreT.CheckT _ _ (HoleT _) _               => apply CheckHoleT
  | |- CoreT.CheckT ?E _ (IdentT ?name _) _       =>
      let s := eval cbv in (sigT E name) in
      lazymatch s with
      | Some (?tys, ?ty) =>
          let tys' := constr:(tys) in
          let ty'  := constr:(ty) in
          eapply (CheckIdentT _ _ name _ tys' ty'); [reflexivity|check]
      | None => fail 100 "unknown term declaration" name
      end
  | |- CoreT.CheckT _ _ (Elem _ _ ) TyProp        => apply CheckElem; check
  | |- CoreT.CheckT _ _ (Leq _ _  ) TyProp        => apply CheckLeq; check
  | |- CoreT.CheckT _ _ (Geq _ _  ) TyProp        => apply CheckGeq; check
  | |- CoreT.CheckT _ _ (Lt _ _   ) TyProp        => apply CheckLt; check
  | |- CoreT.CheckT _ _ (Gt _ _   ) TyProp        => apply CheckGt; check
  | |- CoreT.CheckT _ _ (Equal _ _) TyProp        => apply CheckEqual; check
  | |- CoreT.CheckT _ _ (NotEq _ _) TyProp        => apply CheckNotEq; check
  | |- CoreT.CheckT _ _ (Imp _ _  ) TyProp        => apply CheckImp; check
  | |- CoreT.CheckT _ _ (Iff _ _  ) TyProp        => apply CheckIff; check
  | |- CoreT.CheckT _ _ (And _ _  ) TyProp        => apply CheckAnd; check
  | |- CoreT.CheckT _ _ (Or _ _   ) TyProp        => apply CheckOr; check
  | |- CoreT.CheckT _ _ (Not _    ) TyProp        => apply CheckNot; check
  | |- CoreT.CheckT _ _ (All _    ) TyProp        => apply CheckAll; check
  | |- CoreT.CheckT _ _ (Ex _     ) TyProp        => apply CheckEx; check
  | |- CoreT.CheckT _ _ (Lam _    ) TyClass       => apply CheckLam; check
  | |- CoreT.CheckT _ _ (App _ _  ) TyProp        => apply CheckApp; check
  | |- CoreT.CheckT _ _ (Def _    ) TySet         => apply CheckDef; check
  | |- CoreT.CheckT _ _ (FromC _  ) TySet         => apply CheckFromC; check
  | |- CoreT.CheckTs _ _ NilT []                  => apply CheckTsNil
  | |- CoreT.CheckTs _ _ (ConsT _ _) (_ :: _)     => apply CheckTsCons; check
  | |- CoreT.CheckTs _ _ NilT _                   => cbn; apply CheckTsNil
  | |- CoreT.CheckTs _ _ (ConsT _ _) _            => cbn; apply CheckTsCons; check
  | |- CoreP.CheckP _ _ (HoleP _) _               => apply CheckHoleP; check
  | |- CoreP.CheckP _ _ (AxiomP _) _              => apply CheckAxiomP; check
  | |- CoreP.CheckP ?E ?G (IdentP ?name ?args) _  =>
      tryif
        progress
          (cbv [applyT argT substT Subst.fromT Subst.fromTs
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
            change (CoreP.CheckP E G (IdentP name args) (applyT t' args));
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
