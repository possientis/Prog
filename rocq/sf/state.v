Require Import nat.
Require Import dictionary.


Definition State := TotalMap nat.

Definition emptyState : State := t_empty 0.


Definition x:Key := key 0.
Definition y:Key := key 1.
Definition z:Key := key 2.

