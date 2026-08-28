Require Import ZF.Meta.Term.Decl.
Require Import ZF.Meta.Env.
Require Import ZF.Meta.Term.HasTy.

(* A term declaration is well typed when its body has its declared sort.        *)
Definition HasTyDecl (e:Env) (d:Decl) : Prop :=
  match Term.Decl.body d with
  | Some t => HasTy e (Term.Decl.ctx d) t (Term.Decl.res d)
  | None   => True
  end.
