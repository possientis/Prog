Require Import set.
Require Import empty.

Inductive Unit : Type := unit.


Definition singleton (x:set) : set := mkset Unit (fun _ => x). 

Notation "{ x }" := (singleton x).

Notation "1" := {0}.

