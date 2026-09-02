Require Import ZF.Meta.Env.
Require Import ZF.Meta.Check.
Require Import ZF.Meta.Term.Decl.

(* A term declaration is well typed when its body has its declared sort.        *)
Definition CheckDecl (e:Env) (d:Decl) : Prop :=
  CheckT e (ctxT d) (bodyT d) (resT d).

Definition CheckDeclT := CheckDecl.
