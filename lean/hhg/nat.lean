inductive nat2 : Type
| zero : nat2
| succ : nat2 -> nat2

--#print nat2

inductive aexp : Type
| num : nat -> aexp         -- TODO: need Z
| var : string -> aexp
| add : aexp -> aexp -> aexp
| sub : aexp -> aexp -> aexp
| mul : aexp -> aexp -> aexp
| div : aexp -> aexp -> aexp

