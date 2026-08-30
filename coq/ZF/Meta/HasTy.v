Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

Require Import ZF.Meta.Ctx.
Require Import ZF.Meta.Env.
Require Import ZF.Meta.Proof.Decl.
Require Import ZF.Meta.Syntax.
Require Import ZF.Meta.Term.Decl.
Require Import ZF.Meta.Ty.

Import ListNotations.

Inductive HasTyT (E:Env) : Ctx -> Term -> Ty -> Prop :=
| HasTyBot : forall (G:Ctx),
    HasTyT E G Bot TyProp
| HasTyTop : forall (G:Ctx),
    HasTyT E G Top TyProp
| HasTyVar : forall (G:Ctx) (n:nat) (ty:Ty),
    typeOf G n = Some ty                     ->
    HasTyT E G (Var n) ty
| HasTyHoleT : forall (G:Ctx) (ty:Ty),
    HasTyT E G (HoleT ty) ty
| HasTyIdentT : forall (G:Ctx) (name:string) (args:list Term) (tys:list Ty) (ty:Ty),
    sigT E name = Some (tys,ty)              ->
    HasTyTs E G args tys                     ->
    HasTyT E G (IdentT name args) ty
| HasTyElem : forall (G:Ctx) (x y:Term),
    HasTyT E G x TySet                       ->
    HasTyT E G y TySet                       ->
    HasTyT E G (Elem x y) TyProp
| HasTyLeq : forall (G:Ctx) (x y:Term),
    HasTyT E G x TySet                       ->
    HasTyT E G y TySet                       ->
    HasTyT E G (Leq x y) TyProp
| HasTyGeq : forall (G:Ctx) (x y:Term),
    HasTyT E G x TySet                       ->
    HasTyT E G y TySet                       ->
    HasTyT E G (Geq x y) TyProp
| HasTyLt : forall (G:Ctx) (x y:Term),
    HasTyT E G x TySet                       ->
    HasTyT E G y TySet                       ->
    HasTyT E G (Lt x y) TyProp
| HasTyGt : forall (G:Ctx) (x y:Term),
    HasTyT E G x TySet                       ->
    HasTyT E G y TySet                       ->
    HasTyT E G (Gt x y) TyProp
| HasTyEqual : forall (G:Ctx) (x y:Term),
    HasTyT E G x TySet                       ->
    HasTyT E G y TySet                       ->
    HasTyT E G (Equal x y) TyProp
| HasTyNotEq : forall (G:Ctx) (x y:Term),
    HasTyT E G x TySet                       ->
    HasTyT E G y TySet                       ->
    HasTyT E G (NotEq x y) TyProp
| HasTyImp : forall (G:Ctx) (p q:Term),
    HasTyT E G p TyProp                      ->
    HasTyT E G q TyProp                      ->
    HasTyT E G (Imp p q) TyProp
| HasTyIff : forall (G:Ctx) (p q:Term),
    HasTyT E G p TyProp                      ->
    HasTyT E G q TyProp                      ->
    HasTyT E G (Iff p q) TyProp
| HasTyAnd : forall (G:Ctx) (p q:Term),
    HasTyT E G p TyProp                      ->
    HasTyT E G q TyProp                      ->
    HasTyT E G (And p q) TyProp
| HasTyOr : forall (G:Ctx) (p q:Term),
    HasTyT E G p TyProp                      ->
    HasTyT E G q TyProp                      ->
    HasTyT E G (Or p q) TyProp
| HasTyNot : forall (G:Ctx) (p:Term),
    HasTyT E G p TyProp                      ->
    HasTyT E G (Not p) TyProp
| HasTyAll : forall (G:Ctx) (vty:VarTy) (p:Term),
    HasTyT E (toTy vty :: G) p TyProp        ->
    HasTyT E G (All vty p) TyProp
| HasTyEx : forall (G:Ctx) (vty:VarTy) (p:Term),
    HasTyT E (toTy vty :: G) p TyProp        ->
    HasTyT E G (Ex vty p) TyProp
| HasTyLam : forall (G:Ctx) (p:Term),
    HasTyT E (TySet :: G) p TyProp           ->
    HasTyT E G (Lam p) TyClass
| HasTyApp : forall (G:Ctx) (A x:Term),
    HasTyT E G A TyClass                     ->
    HasTyT E G x TySet                       ->
    HasTyT E G (App A x) TyProp
| HasTyDef : forall (G:Ctx) (A P Q:Term) (p q:Proof),
    HasTyT E G A TyClass                     ->
    HasTyP E G p P                           ->
    HasTyP E G q Q                           ->
    HasTyT E G (Def A p q) TySet
with HasTyTs (E:Env) : Ctx -> list Term -> list Ty -> Prop :=
| HasTyTsNil : forall (G:Ctx),
    HasTyTs E G [] []
| HasTyTsCons : forall (G:Ctx) (t:Term) (ts:list Term) (ty:Ty) (tys:list Ty),
    HasTyT E G t ty                          ->
    HasTyTs E G ts tys                       ->
    HasTyTs E G (t :: ts) (ty :: tys)
with HasTyP (E:Env) : Ctx -> Proof -> Term -> Prop :=
| HasTyHoleP : forall (G:Ctx) (t:Term),
    HasTyT E G t TyProp                      ->
    HasTyP E G (HoleP t) t
| HasTyAxiomP : forall (G:Ctx) (t:Term),
    HasTyT E G t TyProp                      ->
    HasTyP E G (AxiomP t) t
| HasTyIdentP : forall (G:Ctx) (name:string) (args:list Term) (tys:list Ty) (t:Term),
    sigP E name = Some (tys,t)               ->
    HasTyTs E G args tys                     ->
    HasTyP E G (IdentP name args) t
.
