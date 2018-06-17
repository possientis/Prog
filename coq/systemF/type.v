Inductive TVar : Type :=
| tvar : nat -> TVar
.

Inductive FType : Type :=
| VarType : TVar -> FType
| FunType : FType -> FType -> FType
| UniType : TVar -> FType -> FType
.
