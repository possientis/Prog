Require Import Coq.Lists.List.

Require Import ZF.Meta.Ctx.
Require Import ZF.Meta.Syntax.
Require Import ZF.Meta.Ty.

Import ListNotations.

(* A proof declaration records parameters, conclusion and optional proof body.  *)
Record Decl : Type := mkDecl
  { para  : list Ty
  ; concl : Term
  ; body  : option Proof
  }.

(* A proof declaration conclusion is checked in de Bruijn context order.        *)
Definition ctx (d:Decl) : Ctx := rev (para d).

Definition DeclP    := Decl.
Definition mkDeclP  := mkDecl.
Definition paraP    := para.
Definition conclP   := concl.
Definition bodyP    := body.
Definition ctxP     := ctx.
