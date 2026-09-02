Require Import nat.
Require Import dictionary.

Inductive sinstr : Type :=
| SPush : nat -> sinstr
| SLoad : Key -> sinstr
| SPlus : sinstr
| SMinus: sinstr
| SMult : sinstr
.


