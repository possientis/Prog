Require Import ZF.Meta.Env.
Require Import ZF.Meta.HasTy.
Require Import ZF.Meta.Proof.Decl.
Require Import ZF.Meta.Ty.

(* A proof declaration is well typed when its conclusion is a proposition.      *)
Definition HasTyDecl (e:Env) (d:Decl) : Prop :=
  HasTyT e (ctxP d) (conclP d) TyProp /\
  HasTyP e (ctxP d) (bodyP d) (conclP d).

Definition HasTyDeclP := HasTyDecl.
