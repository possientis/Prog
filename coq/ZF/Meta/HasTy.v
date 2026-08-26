Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

Require Import ZF.Meta.Ctx.
Require Import ZF.Meta.Sigs.
Require Import ZF.Meta.Term.
Require Import ZF.Meta.Ty.

Import ListNotations.

Inductive HasTy (S:Sigs) : Ctx -> Term -> Ty -> Prop :=
| HasTyBot : forall (G:Ctx),
    HasTy S G Bot TyProp
| HasTyTop : forall (G:Ctx),
    HasTy S G Top TyProp
| HasTyVar : forall (G:Ctx) (n:nat) (ty:Ty),
    typeOf G n = Some ty ->
    HasTy S G (Var n) ty
| HasTyIdent : forall (G:Ctx) (name:string) (args:list Term)
    (argTys:list Ty) (ty:Ty),
    S name = Some (argTys, ty) ->
    HasTys S G args argTys ->
    HasTy S G (Ident name args) ty
| HasTyElem : forall (G:Ctx) (x y:Term),
    HasTy S G x TySet ->
    HasTy S G y TySet ->
    HasTy S G (Elem x y) TyProp
| HasTyLeq : forall (G:Ctx) (x y:Term),
    HasTy S G x TySet ->
    HasTy S G y TySet ->
    HasTy S G (Leq x y) TyProp
| HasTyGeq : forall (G:Ctx) (x y:Term),
    HasTy S G x TySet ->
    HasTy S G y TySet ->
    HasTy S G (Geq x y) TyProp
| HasTyLt : forall (G:Ctx) (x y:Term),
    HasTy S G x TySet ->
    HasTy S G y TySet ->
    HasTy S G (Lt x y) TyProp
| HasTyGt : forall (G:Ctx) (x y:Term),
    HasTy S G x TySet ->
    HasTy S G y TySet ->
    HasTy S G (Gt x y) TyProp
| HasTyEqual : forall (G:Ctx) (x y:Term),
    HasTy S G x TySet ->
    HasTy S G y TySet ->
    HasTy S G (Equal x y) TyProp
| HasTyNotEq : forall (G:Ctx) (x y:Term),
    HasTy S G x TySet ->
    HasTy S G y TySet ->
    HasTy S G (NotEq x y) TyProp
| HasTyImp : forall (G:Ctx) (p q:Term),
    HasTy S G p TyProp ->
    HasTy S G q TyProp ->
    HasTy S G (Imp p q) TyProp
| HasTyIff : forall (G:Ctx) (p q:Term),
    HasTy S G p TyProp ->
    HasTy S G q TyProp ->
    HasTy S G (Iff p q) TyProp
| HasTyAnd : forall (G:Ctx) (p q:Term),
    HasTy S G p TyProp ->
    HasTy S G q TyProp ->
    HasTy S G (And p q) TyProp
| HasTyOr : forall (G:Ctx) (p q:Term),
    HasTy S G p TyProp ->
    HasTy S G q TyProp ->
    HasTy S G (Or p q) TyProp
| HasTyNot : forall (G:Ctx) (p:Term),
    HasTy S G p TyProp ->
    HasTy S G (Not p) TyProp
| HasTyAll : forall (G:Ctx) (vty:VarTy) (p:Term),
    HasTy S (toTy vty :: G) p TyProp ->
    HasTy S G (All vty p) TyProp
| HasTyEx : forall (G:Ctx) (vty:VarTy) (p:Term),
    HasTy S (toTy vty :: G) p TyProp ->
    HasTy S G (Ex vty p) TyProp
| HasTyThe : forall (G:Ctx) (p:Term),
    HasTy S (TySet :: G) p TyProp ->
    HasTy S G (The p) TySet
| HasTyLam : forall (G:Ctx) (p:Term),
    HasTy S (TySet :: G) p TyProp ->
    HasTy S G (Lam p) TyClass
| HasTyApp : forall (G:Ctx) (A x:Term),
    HasTy S G A TyClass ->
    HasTy S G x TySet ->
    HasTy S G (App A x) TyProp
with HasTys (S:Sigs) : Ctx -> list Term -> list Ty -> Prop :=
| HasTysNil : forall (G:Ctx),
    HasTys S G [] []
| HasTysCons : forall (G:Ctx) (t:Term) (ts:list Term) (ty:Ty)
    (tys:list Ty),
    HasTy S G t ty ->
    HasTys S G ts tys ->
    HasTys S G (t :: ts) (ty :: tys)
.
