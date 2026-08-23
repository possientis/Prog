Require Import Coq.Lists.List.
Require Import ZF.Meta.Ctx.
Require Import ZF.Meta.Ty.

Import ListNotations.

Inductive Term : Type :=
| Bot  : Term
| Var  : nat    -> Term
| Elem : Term   -> Term -> Term
| Imp  : Term   -> Term -> Term
| All  : VarTy  -> Term -> Term
| The  : Term   -> Term
| Lam  : Term   -> Term
| App  : Term   -> Term -> Term
.

Inductive HasTy : Ctx -> Term -> Ty -> Prop :=
| HasTyVar : forall (G:Ctx) (n:nat) (vty:VarTy),
    typeOf G n = Some vty ->
    HasTy G (Var n) (toTy vty)
| HasTyBot : forall (G:Ctx),
    HasTy G Bot TyProp
| HasTyElem : forall (G:Ctx) (x y:Term),
    HasTy G x TySet ->
    HasTy G y TySet ->
    HasTy G (Elem x y) TyProp
| HasTyImp : forall (G:Ctx) (p q:Term),
    HasTy G p TyProp ->
    HasTy G q TyProp ->
    HasTy G (Imp p q) TyProp
| HasTyAll : forall (G:Ctx) (vty:VarTy) (p:Term),
    HasTy (vty :: G) p TyProp ->
    HasTy G (All vty p) TyProp
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
