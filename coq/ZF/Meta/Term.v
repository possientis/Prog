Require Import Coq.Lists.List.
Require Import ZF.Meta.Ctx.
Require Import ZF.Meta.Ty.

Import ListNotations.

Inductive Term : Type :=
| Bot   : Term
| Top   : Term
| Var   : nat    -> Term
| Elem  : Term   -> Term -> Term
| Leq   : Term   -> Term -> Term
| Geq   : Term   -> Term -> Term
| Lt    : Term   -> Term -> Term
| Gt    : Term   -> Term -> Term
| Equal : Term   -> Term -> Term
| NotEq : Term   -> Term -> Term
| Imp   : Term   -> Term -> Term
| Iff   : Term   -> Term -> Term
| And   : Term   -> Term -> Term
| Or    : Term   -> Term -> Term
| Not   : Term   -> Term
| All   : VarTy  -> Term -> Term
| Ex    : VarTy  -> Term -> Term
| The   : Term   -> Term
| Lam   : Term   -> Term
| App   : Term   -> Term -> Term
.

Inductive HasTy : Ctx -> Term -> Ty -> Prop :=
| HasTyBot : forall (G:Ctx),
    HasTy G Bot TyProp
| HasTyTop : forall (G:Ctx),
    HasTy G Top TyProp
| HasTyVar : forall (G:Ctx) (n:nat) (vty:VarTy),
    typeOf G n = Some vty ->
    HasTy G (Var n) (toTy vty)
| HasTyElem : forall (G:Ctx) (x y:Term),
    HasTy G x TySet ->
    HasTy G y TySet ->
    HasTy G (Elem x y) TyProp
| HasTyLeq : forall (G:Ctx) (x y:Term),
    HasTy G x TySet ->
    HasTy G y TySet ->
    HasTy G (Leq x y) TyProp
| HasTyGeq : forall (G:Ctx) (x y:Term),
    HasTy G x TySet ->
    HasTy G y TySet ->
    HasTy G (Geq x y) TyProp
| HasTyLt : forall (G:Ctx) (x y:Term),
    HasTy G x TySet ->
    HasTy G y TySet ->
    HasTy G (Lt x y) TyProp
| HasTyGt : forall (G:Ctx) (x y:Term),
    HasTy G x TySet ->
    HasTy G y TySet ->
    HasTy G (Gt x y) TyProp
| HasTyEqual : forall (G:Ctx) (x y:Term),
    HasTy G x TySet ->
    HasTy G y TySet ->
    HasTy G (Equal x y) TyProp
| HasTyNotEq : forall (G:Ctx) (x y:Term),
    HasTy G x TySet ->
    HasTy G y TySet ->
    HasTy G (NotEq x y) TyProp
| HasTyImp : forall (G:Ctx) (p q:Term),
    HasTy G p TyProp ->
    HasTy G q TyProp ->
    HasTy G (Imp p q) TyProp
| HasTyIff : forall (G:Ctx) (p q:Term),
    HasTy G p TyProp ->
    HasTy G q TyProp ->
    HasTy G (Iff p q) TyProp
| HasTyAnd : forall (G:Ctx) (p q:Term),
    HasTy G p TyProp ->
    HasTy G q TyProp ->
    HasTy G (And p q) TyProp
| HasTyOr : forall (G:Ctx) (p q:Term),
    HasTy G p TyProp ->
    HasTy G q TyProp ->
    HasTy G (Or p q) TyProp
| HasTyNot : forall (G:Ctx) (p:Term),
    HasTy G p TyProp ->
    HasTy G (Not p) TyProp
| HasTyAll : forall (G:Ctx) (vty:VarTy) (p:Term),
    HasTy (vty :: G) p TyProp ->
    HasTy G (All vty p) TyProp
| HasTyEx : forall (G:Ctx) (vty:VarTy) (p:Term),
    HasTy (vty :: G) p TyProp ->
    HasTy G (Ex vty p) TyProp
| HasTyThe : forall (G:Ctx) (p:Term),
    HasTy (VarTySet :: G) p TyProp ->
    HasTy G (The p) TySet
| HasTyLam : forall (G:Ctx) (p:Term),
    HasTy (VarTySet :: G) p TyProp ->
    HasTy G (Lam p) TyClass
| HasTyApp : forall (G:Ctx) (A x:Term),
    HasTy G A TyClass ->
    HasTy G x TySet ->
    HasTy G (App A x) TyProp
.
