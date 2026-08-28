Require Import ZF.Meta.Ctx.
Require Import ZF.Meta.Env.
Require Import ZF.Meta.Term.HasTy.
Require Import ZF.Meta.Term.Syntax.
Require Import ZF.Meta.Ty.

(* A term is well typed in an environment through its signatures view.          *)
Definition HasTyIn (e:Env) (G:Ctx) (t:Term) (ty:Ty) : Prop :=
  HasTy (Env.toSigs e) G t ty.
