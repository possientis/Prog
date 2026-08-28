Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

Require Import ZF.Meta.Ctx.
Require Import ZF.Meta.Env.
Require Import ZF.Meta.Term.Syntax.
Require Import ZF.Meta.Ty.

Import ListNotations.

Inductive HasTy (E:Env) : Ctx -> Term -> Ty -> Prop :=
| HasTyBot : forall (G:Ctx),
    HasTy E G Bot TyProp
| HasTyTop : forall (G:Ctx),
    HasTy E G Top TyProp
| HasTyVar : forall (G:Ctx) (n:nat) (ty:Ty),
    typeOf G n = Some ty                    ->
    HasTy E G (Var n) ty
| HasTyIdent : forall (G:Ctx) (name:string) (args:list Term) (tys:list Ty) (ty:Ty),
    Env.toSigs E name = Some (tys, ty)      ->
    HasTys E G args tys                     ->
    HasTy E G (Ident name args) ty
| HasTyElem : forall (G:Ctx) (x y:Term),
    HasTy E G x TySet                       ->
    HasTy E G y TySet                       ->
    HasTy E G (Elem x y) TyProp
| HasTyLeq : forall (G:Ctx) (x y:Term),
    HasTy E G x TySet                       ->
    HasTy E G y TySet                       ->
    HasTy E G (Leq x y) TyProp
| HasTyGeq : forall (G:Ctx) (x y:Term),
    HasTy E G x TySet                       ->
    HasTy E G y TySet                       ->
    HasTy E G (Geq x y) TyProp
| HasTyLt : forall (G:Ctx) (x y:Term),
    HasTy E G x TySet                       ->
    HasTy E G y TySet                       ->
    HasTy E G (Lt x y) TyProp
| HasTyGt : forall (G:Ctx) (x y:Term),
    HasTy E G x TySet                       ->
    HasTy E G y TySet                       ->
    HasTy E G (Gt x y) TyProp
| HasTyEqual : forall (G:Ctx) (x y:Term),
    HasTy E G x TySet                       ->
    HasTy E G y TySet                       ->
    HasTy E G (Equal x y) TyProp
| HasTyNotEq : forall (G:Ctx) (x y:Term),
    HasTy E G x TySet                       ->
    HasTy E G y TySet                       ->
    HasTy E G (NotEq x y) TyProp
| HasTyImp : forall (G:Ctx) (p q:Term),
    HasTy E G p TyProp                      ->
    HasTy E G q TyProp                      ->
    HasTy E G (Imp p q) TyProp
| HasTyIff : forall (G:Ctx) (p q:Term),
    HasTy E G p TyProp                      ->
    HasTy E G q TyProp                      ->
    HasTy E G (Iff p q) TyProp
| HasTyAnd : forall (G:Ctx) (p q:Term),
    HasTy E G p TyProp                      ->
    HasTy E G q TyProp                      ->
    HasTy E G (And p q) TyProp
| HasTyOr : forall (G:Ctx) (p q:Term),
    HasTy E G p TyProp                      ->
    HasTy E G q TyProp                      ->
    HasTy E G (Or p q) TyProp
| HasTyNot : forall (G:Ctx) (p:Term),
    HasTy E G p TyProp                      ->
    HasTy E G (Not p) TyProp
| HasTyAll : forall (G:Ctx) (vty:VarTy) (p:Term),
    HasTy E (toTy vty :: G) p TyProp        ->
    HasTy E G (All vty p) TyProp
| HasTyEx : forall (G:Ctx) (vty:VarTy) (p:Term),
    HasTy E (toTy vty :: G) p TyProp        ->
    HasTy E G (Ex vty p) TyProp
| HasTyThe : forall (G:Ctx) (p:Term),
    HasTy E (TySet :: G) p TyProp           ->
    HasTy E G (The p) TySet
| HasTyLam : forall (G:Ctx) (p:Term),
    HasTy E (TySet :: G) p TyProp           ->
    HasTy E G (Lam p) TyClass
| HasTyApp : forall (G:Ctx) (A x:Term),
    HasTy E G A TyClass                     ->
    HasTy E G x TySet                       ->
    HasTy E G (App A x) TyProp
with HasTys (E:Env) : Ctx -> list Term -> list Ty -> Prop :=
| HasTysNil : forall (G:Ctx),
    HasTys E G [] []
| HasTysCons : forall (G:Ctx) (t:Term) (ts:list Term) (ty:Ty) (tys:list Ty),
    HasTy E G t ty                          ->
    HasTys E G ts tys                       ->
    HasTys E G (t :: ts) (ty :: tys)
.
