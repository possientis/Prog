Require Import set.

Inductive Void : Type :=.

Definition absurd (x:Void) : set :=
    match x with
    end.

Definition zero : set := mkset Void absurd.

Notation "0" := (zero). 


