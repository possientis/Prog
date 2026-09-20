Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

Require Import ZF.Meta.Apply.
Require Import ZF.Meta.Check.CoreT.
Require Import ZF.Meta.Ctx.
Require Import ZF.Meta.Env.
Require Import ZF.Meta.Name.
Require Import ZF.Meta.SyntaxT.
Require Import ZF.Meta.SyntaxP.
Require Import ZF.Meta.Ty.

Import ListNotations.
Open Scope string_scope.

Inductive CheckP (E:Env) : Ctx -> Proof -> Term -> Prop :=
| CheckHoleP : forall (G:Ctx) (t:Term),
    CheckT E G t TyProp                      ->
    CheckP E G (HoleP t) t
| CheckAxiomP : forall (G:Ctx) (t:Term),
    CheckT E G t TyProp                      ->
    CheckP E G (AxiomP t) t
| CheckIdentP : forall (G:Ctx) (name:Name) (args:Terms)
    (tys:list Ty) (t:Term),
    sigP E name = Some (tys,t)               ->
    CheckTs E G args tys                     ->
    CheckP E G (IdentP name args) (applyT t args)
.
