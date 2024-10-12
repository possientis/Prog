Declare Scope Fol_Syntax_scope.
Open Scope Fol_Syntax_scope.

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
Arguments Elem {v}.
Arguments Imp  {v}.
Arguments All  {v}.

Notation "x :< y" := (Elem x y)
  (at level 1, no associativity)      : Fol_Syntax_scope.

Notation "p :-> q" := (Imp p q)
  (at level 20, right associativity)  : Fol_Syntax_scope.

Notation "¬ p" := (Imp p Bot)
  (at level 1, no associativity)      : Fol_Syntax_scope.

Definition bot (v:Type) : P v := Bot.

Arguments bot {v}.

Definition or (v:Type) (p q: P v) : P v := ¬p :-> q.

Arguments or {v}.

Definition and (v:Type) (p q: P v) : P v := ¬(p :-> ¬q).

Arguments and {v}.

Definition equiv (v:Type) (p q:P v) : P v := and (p :-> q) (q :-> p).

Arguments equiv {v}.

Notation "p :-: q" := (equiv p q)
  (at level 20, right associativity)  : Fol_Syntax_scope.
