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
Proposition PreserveT :
  forall (E:Env) (G D:Ctx) (t:Term) (ty:Ty) (ts:Terms),
    Check E                                               ->
    CheckT E (G ++ D) t ty                                ->
    CheckTs E D ts (rev G)                                ->
    CheckT E D (applyT t ts) ty.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros E G D t ty ts H1 H2 H3.
  apply (Check.Subst.FromT E) with (G := []) (M := G) (D := D); assumption.
Qed.
