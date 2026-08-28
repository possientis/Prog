Require Import Coq.Lists.List.
Require Import Coq.Strings.String.

Require Import ZF.Meta.Term.Syntax.

Import ListNotations.

Inductive Proof : Type :=
| Ident : string -> list Term -> Proof
.
