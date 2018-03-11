Require Import nat.

Inductive aexp : Type :=
| ANum   : nat -> aexp
| APlus  : aexp -> aexp -> aexp
| AMinus : aexp -> aexp -> aexp
| AMult  : aexp -> aexp -> aexp
.


Inductive bexp : Type :=
| BTrue  : bexp
| BFalse : bexp
| BEq    : aexp -> aexp -> bexp
| BLe    : aexp -> aexp -> bexp
| BNot   : bexp -> bexp
| BAnd   : bexp -> bexp -> bexp
.
