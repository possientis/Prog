Require Import ZF.Meta.Env.
Require Import ZF.Meta.HasTy.
Require Import ZF.Meta.Term.Decl.

(* A term declaration is well typed when its body has its declared sort.        *)
Definition HasTyDecl (e:Env) (d:Decl) : Prop :=
  HasTyT e (ctxT d) (bodyT d) (resT d).

Definition HasTyDeclT := HasTyDecl.
