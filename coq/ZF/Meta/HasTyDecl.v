Require Import ZF.Meta.Decl.
Require Import ZF.Meta.Env.
Require Import ZF.Meta.HasTy.

(* A declaration is well typed when its modeled body has its declared sort.     *)
Definition HasTyDecl (e:Env) (d:Decl) : Prop :=
  match Decl.body d with
  | Some t => HasTy (Env.toSigs e) (Decl.ctx d) t (Decl.res d)
  | None   => True
  end.
