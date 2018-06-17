Require Import type.

Inductive Var : Type :=
| var : nat -> FType -> Var
.


Inductive Term : Type :=
| VarTerm : Var -> Term
| AbsTerm : Var -> Term -> Term
| AppTerm : Term -> Term -> Term
| TAbsTerm: TVar -> Term -> Term
| TAppTerm: Term -> FType -> Term
.



