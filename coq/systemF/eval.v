Require Import term.
Require Import value.

Inductive eval : Term -> Term -> Prop :=
| EApp1 : forall t1 t1' t2, 
    eval t1 t1' -> eval (AppTerm t1 t2) (AppTerm t1' t2)
| EApp2 : forall v1 t2 t2',
    value v1 -> eval t2 t2' -> eval (AppTerm v1 t2) (AppTerm v1 t2')
.
