Require Import Coq.Lists.List.

Require Import ZF.Meta.Ctx.
Require Import ZF.Meta.Syntax.
Require Import ZF.Meta.Ty.

Import ListNotations.

(* A proof declaration records parameters, conclusion and proof body.           *)
Record DeclP : Type := mkDeclP
  { paraP  : list Ty
  ; conclP : Term
  ; bodyP  : Proof
  }.

(* A proof declaration conclusion is checked in de Bruijn context order.        *)
Definition ctxP (d:DeclP) : Ctx := rev (paraP d).
