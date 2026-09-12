Require Import Coq.Lists.List.

Require Import ZF.Meta.Apply.
Require Import ZF.Meta.Check.Core.
Require Import ZF.Meta.Check.Env.
Require Import ZF.Meta.Check.Subst.
Require Import ZF.Meta.Ctx.
Require Import ZF.Meta.Env.
Require Import ZF.Meta.Subst.
Require Import ZF.Meta.Syntax.
Require Import ZF.Meta.Ty.

Import ListNotations.

(* Applying checked arguments to a checked term preserves its sort.             *)
Proposition ApplyT :
  forall (E:Env) (G D:Ctx) (t:Term) (ty:Ty) (ts:Terms),
    Check E                                                             ->
    CheckT E (D ++ G) t ty                                              ->
    CheckTs E G ts (rev D)                                              ->
    CheckT E G (applyT t ts) ty.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros E G D t ty ts H1 H2 H3.
  unfold applyT, substT.
  apply (Check.Subst.FromT E) with (G := []) (M := D) (D := G); assumption.
Qed.
