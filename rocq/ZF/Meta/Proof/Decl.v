Require Import Coq.Lists.List.

Require Import ZF.Meta.Ctx.
Require Import ZF.Meta.Syntax.
Require Import ZF.Meta.Ty.

Import ListNotations.

(* A proof declaration records parameters, conclusion and proof body.           *)
Record Decl : Type := mkDecl
  { paraP  : list Ty
  ; conclP : Term
  ; bodyP  : Proof
  }.

(* A proof declaration conclusion is checked in de Bruijn context order.        *)
Definition ctx (d:Decl) : Ctx := rev (paraP d).

Definition DeclP    := Decl.
Definition mkDeclP  := mkDecl.
Definition ctxP     := ctx.
