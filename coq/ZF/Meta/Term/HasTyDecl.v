Require Import ZF.Meta.Term.Decl.
Require Import ZF.Meta.Env.
Require Import ZF.Meta.Term.HasTy.

(* A term declaration is well typed when its body has its declared sort.        *)
Definition HasTyDecl (e:Env) (d:Decl) : Prop :=
  match Decl.body d with
  | Some t => HasTy (Env.toSigs e) (Decl.ctx d) t (Decl.res d)
  | None   => True
  end.
