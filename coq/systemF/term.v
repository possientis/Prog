Require Import Arith.
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

Definition varEqual (x x':Var) : bool :=
    match x, x' with
    | (var x T), (var x' T') => (beq_nat x x') && (FTypeEqual T T')
    end.



