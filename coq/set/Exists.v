Require Import set.

Inductive Exists (P:set -> Prop) : set -> Prop :=
| ExistsH : forall (x:set) (ys:set), P x         -> Exists P (Cons x ys)
| ExistsT : forall (x:set) (ys:set), Exists P ys -> Exists P (Cons x ys)
.


