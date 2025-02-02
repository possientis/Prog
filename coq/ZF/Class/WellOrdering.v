Require Import ZF.Class.
Require Import ZF.Class.Founded.
Require Import ZF.Class.Total.

(* Predicate expressing the fact that R is a well-ordering class on A.          *)
(* R is a well-ordering on A iff it is founded on A and total on A.             *)
Definition WellOrdering (R A:Class) : Prop :=  Founded R A /\ Total R A.
