
Inductive Partial (P:Prop) : Set :=
| Proved: P -> Partial P
| Uncertain: Partial P
.


