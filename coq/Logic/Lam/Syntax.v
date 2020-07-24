(* The type 'v' represents the set of variables symbols.        *)
(* The type T v is the set of lambda terms with variables in v. *)

Inductive T (v:Type) : Type :=
| Var : v -> T v                    (* variable                 *)
| App : T v -> T v -> T v           (* application              *)
| Lam : v -> T v -> T v             (* lambda abstraction       *)
.

Arguments Var {v} _.
Arguments App {v} _ _.
Arguments Lam {v} _ _.


