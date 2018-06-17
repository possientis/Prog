Require Import type.
Require Import term.

Inductive Context : Type :=
| CNil      : Context
| vCons     : Var -> Context -> Context
| tCons     : TVar -> Context -> Context
.
