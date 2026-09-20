Require Import Coq.Lists.List.

Require Import ZF.Meta.Apply.
Require Import ZF.Meta.Check.CoreT.
Require Import ZF.Meta.Check.CoreP.
Require Import ZF.Meta.Ctx.
Require Import ZF.Meta.Env.
Require Import ZF.Meta.Name.
Require Import ZF.Meta.SyntaxT.
Require Import ZF.Meta.SyntaxP.
Require Import ZF.Meta.Ty.

Import ListNotations.

(* Checked proofs have an induction principle over their checked propositions.  *)
Proposition Induction :
  forall
    (P:Env -> Ctx -> Term -> Ty -> Prop)
    (Q:Env -> Ctx -> Terms -> list Ty -> Prop)
    (R:Env -> Ctx -> Proof -> Term -> Prop),
    (forall (E:Env) (G:Ctx) (t:Term) (ty:Ty),
      CheckT E G t ty -> P E G t ty)                                          ->
    (forall (E:Env) (G:Ctx) (ts:Terms) (tys:list Ty),
      CheckTs E G ts tys -> Q E G ts tys)                                     ->
    (forall (E:Env) (G:Ctx) (t:Term),
      CheckT E G t TyProp                                                     ->
      P E G t TyProp                                                          ->
      R E G (HoleP t) t)                                                      ->
    (forall (E:Env) (G:Ctx) (t:Term),
      CheckT E G t TyProp                                                     ->
      P E G t TyProp                                                          ->
      R E G (AxiomP t) t)                                                     ->
    (forall (E:Env) (G:Ctx) (name:Name) (args:Terms) (tys:list Ty) (t:Term),
      sigP E name = Some (tys,t)                                              ->
      CheckTs E G args tys                                                    ->
      Q E G args tys                                                          ->
      R E G (IdentP name args) (applyT t args))                               ->
    forall (E:Env) (G:Ctx) (p:Proof) (t:Term),
      CheckP E G p t -> R E G p t.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros P Q R H1 H2 H3 H4 H5 E G p t H6.
  destruct H6 as [G t H6|G t H6|G name args tys t H6 H7].
  - apply H3. 1: assumption. apply H1. assumption.
  - apply H4. 1: assumption. apply H1. assumption.
  - apply (H5 E G name args tys t). 1: assumption. 1: assumption.
    apply H2. assumption.
Qed.
