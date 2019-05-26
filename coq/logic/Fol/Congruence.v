Require Import Relation.
Require Import Fol.P.

Definition congruent (v:Type) (r:Rel (P v)) : Prop := 
    (forall (p1 p2 q1 q2:P v), r p1 q1 -> r p2 q2 -> r (Imp p1 p2) (Imp q1 q2)) /\
    (forall (x:v) (p1 q1:P v), r p1 q1 -> r (All x p1) (All x q1)).

Arguments congruent {v} _.

Definition congruence (v:Type) (r:Rel (P v)) : Prop :=
   equivalence r /\ congruent r. 

Arguments congruence {v} _.
