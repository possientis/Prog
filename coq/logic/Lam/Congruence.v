Require Import Relation.
Require Import Lam.T.

Definition congruent (v:Type) (r:Rel (T v)) : Prop := 
    (forall (s1 s2 t1 t2:T v), r s1 t1 -> r s2 t2 -> r (App s1 s2) (App t1 t2)) /\
    (forall (x:v) (s1 t1:T v), r s1 t1 -> r (Lam x s1) (Lam x t1)).

Arguments congruent {v} _.

Definition congruence (v:Type) (r:Rel (T v)) : Prop :=
   equivalence r /\ congruent r. 

Arguments congruence {v} _.
