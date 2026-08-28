Require Import Coq.Lists.List.

Require Import ZF.Meta.Ctx.
Require Import ZF.Meta.Signature.
Require Import ZF.Meta.Term.Syntax.
Require Import ZF.Meta.Ty.

Import ListNotations.

(* A term declaration records parameters, result sort and optional body.        *)
Record Decl : Type := mkDecl
  { para : list Ty
  ; res  : Ty
  ; body : option Term
  }.

(* The signature of a term declaration seen by identifier application.          *)
Definition signature (d:Decl) : Signature :=
  (para d, res d).

(* A term declaration body is checked in de Bruijn context order.               *)
Definition ctx (d:Decl) : Ctx := rev (para d).
