Require Import ZF.Meta.DeclTerm.
Require Import ZF.Meta.Env.
Require Import ZF.Meta.HasTy.

(* A term declaration is well typed when its body has its declared sort.        *)
Definition HasTyDeclTerm (e:Env) (d:DeclTerm) : Prop :=
  match DeclTerm.body d with
  | Some t => HasTy (Env.toSigs e) (DeclTerm.ctx d) t (DeclTerm.res d)
  | None   => True
  end.
