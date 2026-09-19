Require Import Coq.Lists.List.

Require Import ZF.Meta.Check.Core.
Require Import ZF.Meta.Check.DeclP.
Require Import ZF.Meta.Check.DeclT.
Require Import ZF.Meta.DeclP.
Require Import ZF.Meta.DeclT.
Require Import ZF.Meta.Syntax.
Require Import ZF.Meta.Ty.

Import ListNotations.

(* A tactic for routine syntax-directed checker obligations.                    *)
Ltac check :=
  match goal with
  | |- Core.CheckT _ _ Bot TyProp => apply CheckBot
  | |- Core.CheckT _ _ Top TyProp => apply CheckTop
  | |- Core.CheckT _ _ (Var _) _ => apply CheckVar; reflexivity
  | |- Core.CheckT _ _ (HoleT _) _ => apply CheckHoleT
  | |- Core.CheckT _ _ (IdentT _ _) _ => eapply CheckIdentT; [reflexivity|check]
  | |- Core.CheckT _ _ (Elem _ _) TyProp => apply CheckElem; check
  | |- Core.CheckT _ _ (Leq _ _) TyProp => apply CheckLeq; check
  | |- Core.CheckT _ _ (Geq _ _) TyProp => apply CheckGeq; check
  | |- Core.CheckT _ _ (Lt _ _) TyProp => apply CheckLt; check
  | |- Core.CheckT _ _ (Gt _ _) TyProp => apply CheckGt; check
  | |- Core.CheckT _ _ (Equal _ _) TyProp => apply CheckEqual; check
  | |- Core.CheckT _ _ (NotEq _ _) TyProp => apply CheckNotEq; check
  | |- Core.CheckT _ _ (Imp _ _) TyProp => apply CheckImp; check
  | |- Core.CheckT _ _ (Iff _ _) TyProp => apply CheckIff; check
  | |- Core.CheckT _ _ (And _ _) TyProp => apply CheckAnd; check
  | |- Core.CheckT _ _ (Or _ _) TyProp => apply CheckOr; check
  | |- Core.CheckT _ _ (Not _) TyProp => apply CheckNot; check
  | |- Core.CheckT _ _ (All _) TyProp => apply CheckAll; check
  | |- Core.CheckT _ _ (Ex _) TyProp => apply CheckEx; check
  | |- Core.CheckT _ _ (Lam _) TyClass => apply CheckLam; check
  | |- Core.CheckT _ _ (App _ _) TyProp => apply CheckApp; check
  | |- Core.CheckT _ _ (Def _ _ _) TySet => apply CheckDef; check
  | |- Core.CheckT _ _ (FromC _ _) TySet => apply CheckFromC; check
  | |- Core.CheckTs _ _ NilT [] => apply CheckTsNil
  | |- Core.CheckTs _ _ (ConsT _ _) (_ :: _) => apply CheckTsCons; check
  | |- Core.CheckTs _ _ NilT _ => cbn; apply CheckTsNil
  | |- Core.CheckTs _ _ (ConsT _ _) _ => cbn; apply CheckTsCons; check
  | |- Core.CheckP _ _ (HoleP _) _ => apply CheckHoleP; check
  | |- Core.CheckP _ _ (AxiomP _) _ => apply CheckAxiomP; check
  | |- Core.CheckP _ _ (IdentP _ _) _ => eapply CheckIdentP; [reflexivity|check]
  end.

Ltac checkT :=
  cbv [DeclT.CheckT args fromList ctxT paraT resT bodyT];
  check.

Ltac checkP :=
  cbv [DeclP.CheckP args fromList ctxP conclP paraP bodyP];
  split; check.
