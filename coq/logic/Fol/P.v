(* The type 'v' represents the set of variables symbols.        *)
(* The type P v is the set of set theoretic first order         *)
(* propositions with variables in v.                            *)


Inductive P (v:Type) : Type :=
| Bot  : P v                        (* bottom                   *)
| Elem : v -> v -> P v              (* x `Elem` y               *)
| Imp  : P v -> P v -> P v          (* implication              *)
| All  : v -> P v -> P v            (* quantification           *)
.

Arguments Bot  {v}.
Arguments Elem {v} _ _.
Arguments Imp  {v} _ _.
Arguments All  {v} _ _.


