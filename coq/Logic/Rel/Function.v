Require Import Logic.Rel.R.
Require Import Logic.Rel.Total.
Require Import Logic.Rel.Functional.


Definition Function (a b:Type) (r:R a b) : Prop := Functional r /\ Total r.

Arguments Function {a} {b}.


