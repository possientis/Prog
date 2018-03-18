Require Import nat.
Require Import syntax.

Inductive aevalR:aexp -> nat -> Prop :=
| E_ANum : forall (n:nat), aevalR (ANum n) n
| E_APlus: forall (n1 n2:nat) (a1 a2:aexp), 
    aevalR a1 n1 -> aevalR a2 n2 -> aevalR (APlus a1 a2) (n1 + n2)
| E_AMinus: forall (n1 n2:nat) (a1 a2:aexp), 
    aevalR a1 n1 -> aevalR a2 n2 -> aevalR (AMinus a1 a2) (n1 - n2)
| E_AMult: forall (n1 n2:nat) (a1 a2:aexp), 
    aevalR a1 n1 -> aevalR a2 n2 -> aevalR (AMult a1 a2) (n1 * n2)
.

Notation "e \\ n" := (aevalR e n) (at level 50, no associativity) : type_scope.
