(* The type 'v' represents the set of variables symbols.        *)
(* The type P v is the set of lambda terms with variables in v. *)


Inductive P (v:Type) : Type :=
| Var : v -> P v                    (* variable                 *)
| App : P v -> P v -> P v           (* application              *)
| Lam : v -> P v -> P v             (* lambda abstraction       *)
.

Arguments Var {v} _.
Arguments App {v} _ _.
Arguments Lam {v} _ _.



