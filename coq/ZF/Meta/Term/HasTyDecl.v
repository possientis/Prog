Require Import ZF.Meta.Env.
Require Import ZF.Meta.HasTy.
Require Import ZF.Meta.Term.Decl.

(* A term declaration is well typed when its body has its declared sort.        *)
Definition HasTyDecl (e:Env) (d:Decl) : Prop :=
  match bodyT d with
  | Some t => HasTyT e (ctxT d) t (resT d)
  | None   => True
  end.

Definition HasTyDeclT := HasTyDecl.
