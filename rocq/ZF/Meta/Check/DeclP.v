Require Import ZF.Meta.Check.Core.
Require Import ZF.Meta.DeclP.
Require Import ZF.Meta.Env.
Require Import ZF.Meta.Ty.

(* A proof declaration is checked when its conclusion has a proof.              *)
Definition CheckP (E:Env) (d:DeclP) : Prop :=
  CheckT E (ctxP d) (conclP d) TyProp /\
  CheckP E (ctxP d) (bodyP d) (conclP d).
