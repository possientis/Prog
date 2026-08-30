Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

Require Import ZF.Meta.Ctx.
Require Import ZF.Meta.Env.
Require Import ZF.Meta.Proof.Decl.
Require Import ZF.Meta.Syntax.
Require Import ZF.Meta.Term.Decl.
Require Import ZF.Meta.Ty.

Import ListNotations.

Inductive CheckT (E:Env) : Ctx -> Term -> Ty -> Prop :=
| CheckBot : forall (G:Ctx),
    CheckT E G Bot TyProp
| CheckTop : forall (G:Ctx),
    CheckT E G Top TyProp
| CheckVar : forall (G:Ctx) (n:nat) (ty:Ty),
    typeOf G n = Some ty                     ->
    CheckT E G (Var n) ty
| CheckHoleT : forall (G:Ctx) (ty:Ty),
    CheckT E G (HoleT ty) ty
| CheckIdentT : forall (G:Ctx) (name:string) (args:list Term) (tys:list Ty) (ty:Ty),
    sigT E name = Some (tys,ty)              ->
    CheckTs E G args tys                     ->
    CheckT E G (IdentT name args) ty
| CheckElem : forall (G:Ctx) (x y:Term),
    CheckT E G x TySet                       ->
    CheckT E G y TySet                       ->
    CheckT E G (Elem x y) TyProp
| CheckLeq : forall (G:Ctx) (x y:Term),
    CheckT E G x TySet                       ->
    CheckT E G y TySet                       ->
    CheckT E G (Leq x y) TyProp
| CheckGeq : forall (G:Ctx) (x y:Term),
    CheckT E G x TySet                       ->
    CheckT E G y TySet                       ->
    CheckT E G (Geq x y) TyProp
| CheckLt : forall (G:Ctx) (x y:Term),
    CheckT E G x TySet                       ->
    CheckT E G y TySet                       ->
    CheckT E G (Lt x y) TyProp
| CheckGt : forall (G:Ctx) (x y:Term),
    CheckT E G x TySet                       ->
    CheckT E G y TySet                       ->
    CheckT E G (Gt x y) TyProp
| CheckEqual : forall (G:Ctx) (x y:Term),
    CheckT E G x TySet                       ->
    CheckT E G y TySet                       ->
    CheckT E G (Equal x y) TyProp
| CheckNotEq : forall (G:Ctx) (x y:Term),
    CheckT E G x TySet                       ->
    CheckT E G y TySet                       ->
    CheckT E G (NotEq x y) TyProp
| CheckImp : forall (G:Ctx) (p q:Term),
    CheckT E G p TyProp                      ->
    CheckT E G q TyProp                      ->
    CheckT E G (Imp p q) TyProp
| CheckIff : forall (G:Ctx) (p q:Term),
    CheckT E G p TyProp                      ->
    CheckT E G q TyProp                      ->
    CheckT E G (Iff p q) TyProp
| CheckAnd : forall (G:Ctx) (p q:Term),
    CheckT E G p TyProp                      ->
    CheckT E G q TyProp                      ->
    CheckT E G (And p q) TyProp
| CheckOr : forall (G:Ctx) (p q:Term),
    CheckT E G p TyProp                      ->
    CheckT E G q TyProp                      ->
    CheckT E G (Or p q) TyProp
| CheckNot : forall (G:Ctx) (p:Term),
    CheckT E G p TyProp                      ->
    CheckT E G (Not p) TyProp
| CheckAll : forall (G:Ctx) (vty:VarTy) (p:Term),
    CheckT E (toTy vty :: G) p TyProp        ->
    CheckT E G (All vty p) TyProp
| CheckEx : forall (G:Ctx) (vty:VarTy) (p:Term),
    CheckT E (toTy vty :: G) p TyProp        ->
    CheckT E G (Ex vty p) TyProp
| CheckLam : forall (G:Ctx) (p:Term),
    CheckT E (TySet :: G) p TyProp           ->
    CheckT E G (Lam p) TyClass
| CheckApp : forall (G:Ctx) (A x:Term),
    CheckT E G A TyClass                     ->
    CheckT E G x TySet                       ->
    CheckT E G (App A x) TyProp
| CheckDef : forall (G:Ctx) (A P Q:Term) (p q:Proof),
    CheckT E G A TyClass                     ->
    CheckP E G p P                           ->
    CheckP E G q Q                           ->
    CheckT E G (Def A p q) TySet
with CheckTs (E:Env) : Ctx -> list Term -> list Ty -> Prop :=
| CheckTsNil : forall (G:Ctx),
    CheckTs E G [] []
| CheckTsCons : forall (G:Ctx) (t:Term) (ts:list Term) (ty:Ty) (tys:list Ty),
    CheckT E G t ty                          ->
    CheckTs E G ts tys                       ->
    CheckTs E G (t :: ts) (ty :: tys)
with CheckP (E:Env) : Ctx -> Proof -> Term -> Prop :=
| CheckHoleP : forall (G:Ctx) (t:Term),
    CheckT E G t TyProp                      ->
    CheckP E G (HoleP t) t
| CheckAxiomP : forall (G:Ctx) (t:Term),
    CheckT E G t TyProp                      ->
    CheckP E G (AxiomP t) t
| CheckIdentP : forall (G:Ctx) (name:string) (args:list Term) (tys:list Ty) (t:Term),
    sigP E name = Some (tys,t)               ->
    CheckTs E G args tys                     ->
    CheckP E G (IdentP name args) t
.
