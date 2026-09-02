Declare Scope Prop_Syntax_scope.

(* Given a type v of all propositional variables, defines the tyoe P v of all   *)
(* formulas of propositional logic with atoms in v                              *)
Inductive P (v:Type) : Type :=
| Bot : P v
| Var : v -> P v
| Imp : P v -> P v -> P v
.

Arguments Bot {v}.
Arguments Var {v}.
Arguments Imp {v}.

Notation "p :-> q" := (Imp p q)
  (at level 20, right associativity)  : Prop_Syntax_scope.

Notation "¬ p" := (Imp p Bot)
  (at level 1, no associativity)      : Prop_Syntax_scope.

Notation "' p" := (Var p)
  (at level 1, no associativity)      : Prop_Syntax_scope.

Definition bot (v:Type) : P v := Bot.

Arguments bot {v}.

Open Scope Prop_Syntax_scope.

Definition or (v:Type) (p q: P v) : P v := ¬p :-> q.

Arguments or {v}.

Definition and (v:Type) (p q: P v) : P v := ¬(p :-> ¬q).

Arguments and {v}.
