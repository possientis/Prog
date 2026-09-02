Require Import ZF.Meta.Env.
Require Import ZF.Meta.Check.
Require Import ZF.Meta.Proof.Decl.
Require Import ZF.Meta.Ty.

(* A proof declaration is well typed when its conclusion is a proposition.      *)
Definition CheckDecl (e:Env) (d:Decl) : Prop :=
  CheckT e (ctxP d) (conclP d) TyProp /\
  CheckP e (ctxP d) (bodyP d) (conclP d).

Definition CheckDeclP := CheckDecl.
