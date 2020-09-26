
Require Import Logic.Rel.R.
Require Import Logic.Rel.Intersect.

Definition incl (a b:Type) (r s:R a b) : Prop := r = inter r s.
Arguments incl {a} {b}.

Notation "r <= s" := (incl r s)
    (at level 70, no associativity) : Rel_Include_scope.

Open Scope Rel_Include_scope.


