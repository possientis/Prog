Require Import ZF.Meta.Env.
Require Import ZF.Meta.HasTy.
Require Import ZF.Meta.Proof.Decl.
Require Import ZF.Meta.Ty.

(* A proof declaration is well typed when its conclusion is a proposition.      *)
Definition HasTyDecl (e:Env) (d:Decl) : Prop :=
  HasTyT e (ctxP d) (conclP d) TyProp /\
  match bodyP d with
  | Some p => HasTyP e (ctxP d) p
  | None   => True
  end.

Definition HasTyDeclP := HasTyDecl.
