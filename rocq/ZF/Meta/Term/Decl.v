Require Import Coq.Lists.List.

Require Import ZF.Meta.Ctx.
Require Import ZF.Meta.Syntax.
Require Import ZF.Meta.Ty.

Import ListNotations.

(* A term declaration records parameters, result sort and body.                 *)
Record Decl : Type := mkDecl
  { paraT : list Ty
  ; resT  : Ty
  ; bodyT : Term
  }.

(* A term declaration body is checked in de Bruijn context order.               *)
Definition ctx (d:Decl) : Ctx := rev (paraT d).

Definition DeclT      := Decl.
Definition mkDeclT    := mkDecl.
Definition ctxT       := ctx.
