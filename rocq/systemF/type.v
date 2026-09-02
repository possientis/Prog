Require Import Arith.
Import Nat.

Inductive TVar : Type :=
| tvar : nat -> TVar
.

Inductive FType : Type :=
| VarType : TVar -> FType
| FunType : FType -> FType -> FType
| UniType : TVar -> FType -> FType
.

Definition tvarEqual (X Y:TVar) : bool :=
    match X, Y with
    | (tvar x), (tvar y)    => if (eqb x y) then true else false
    end.

Fixpoint FTypeEqual (T T':FType) : bool :=
    match T with
    | VarType X     => match T' with 
                       | VarType Y     => tvarEqual X Y
                       | _             => false
                       end
    | FunType T1 T2 => match T' with
                       | FunType S1 S2 => andb (FTypeEqual T1 S1)(FTypeEqual T2 S2)
                       | _             => false
                       end
    | UniType X T1  => match T' with (* equality stricter than alpha equivalence *)
                       | UniType Y S1  => andb (tvarEqual X Y)(FTypeEqual T1 S1)
                       | _             => false
                       end
    end.





