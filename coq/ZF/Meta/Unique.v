Require Import ZF.Meta.Shift.
Require Import ZF.Meta.Syntax.

Definition Unique (A:Term) : Term :=
  All
    (All
      (Imp
        (App (ShiftT 2 A) (Var 1))
        (Imp
          (App (ShiftT 2 A) (Var 0))
          (Equal (Var 1) (Var 0))))).
