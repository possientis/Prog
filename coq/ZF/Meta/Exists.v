Require Import ZF.Meta.Shift.
Require Import ZF.Meta.Syntax.

Definition Exists (A:Term) : Term := Ex (App (ShiftT 1 A) (Var 0)).

