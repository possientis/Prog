Require Import ZF.Meta.Check.
Require Import ZF.Meta.DeclT.
Require Import ZF.Meta.Env.

(* A term declaration is checked when its body has its declared sort.           *)
Definition CheckT (E:Env) (d:DeclT) : Prop :=
  CheckT E (ctxT d) (bodyT d) (resT d).
