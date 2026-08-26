Require Import Coq.Lists.List.

Require Import ZF.Meta.Ctx.
Require Import ZF.Meta.Term.
Require Import ZF.Meta.Ty.

Import ListNotations.

(* A declaration records source-order parameter sorts, result sort and a body.  *)
Record Decl : Type := mkDecl {
  params : list Ty;
  result : Ty;
  body   : option Term
}.

(* The arity of a declaration is the signature seen by identifier application.  *)
Definition arity (d:Decl) : list Ty * Ty :=
  (params d, result d).

(* A declaration body is checked under parameters in de Bruijn context order.   *)
Definition ctx (d:Decl) : Ctx := rev (params d).
