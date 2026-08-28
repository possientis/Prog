Require Import Coq.Lists.List.

Require Import ZF.Meta.Ctx.
Require Import ZF.Meta.Syntax.
Require Import ZF.Meta.Ty.

Import ListNotations.

(* A term declaration records parameters, result sort and optional body.        *)
Record Decl : Type := mkDecl
  { para : list Ty
  ; res  : Ty
  ; body : option Term
  }.

(* A term declaration body is checked in de Bruijn context order.               *)
Definition ctx (d:Decl) : Ctx := rev (para d).

Definition DeclT      := Decl.
Definition mkDeclT    := mkDecl.
Definition paraT      := para.
Definition resT       := res.
Definition bodyT      := body.
Definition ctxT       := ctx.
