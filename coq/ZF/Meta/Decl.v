Require Import Coq.Lists.List.

Require Import ZF.Meta.Ctx.
Require Import ZF.Meta.Signature.
Require Import ZF.Meta.Term.
Require Import ZF.Meta.Ty.

Import ListNotations.

(* A declaration records source-order parameter sorts, result sort and a body.  *)
Record Decl : Type := mkDecl {
  para : list Ty;
  res  : Ty;
  body : option Term
}.

(* The signature of a declaration seen by identifier application.               *)
Definition signature (d:Decl) : Signature :=
  (para d, res d).

(* A declaration body is checked under parameters in de Bruijn context order.   *)
Definition ctx (d:Decl) : Ctx := rev (para d).
