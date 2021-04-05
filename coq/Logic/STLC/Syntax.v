
(* Type language where possible base types are in type b                        *)
Inductive T (b:Type) : Type :=
| Base : b -> T b
| Fun  : T b -> T b -> T b
.

Arguments Base {b}.
Arguments Fun  {b}.

(* Expression language for base types in b and variables in v                   *) 
Inductive Exp (b v:Type) : Type :=
| Ann : Exp b v -> T b -> Exp b v           (* annotated term                   *)
| Var : v -> Exp b v                        (* variable                         *)
| App : Exp b v -> Exp b v -> Exp b v       (* application                      *)
| Lam : v -> Exp b v -> Exp b v             (* lambda abstraction               *)
.

Arguments Ann {b} {v}.
Arguments Var {b} {v}.
Arguments App {b} {v}.
Arguments Lam {b} {v}.

Notation "t :: Ty" := (Ann t Ty)        : STLC_Syntax_scope.

Notation "t $ t'" := (App t t')
    (at level 10, left associativity)   : STLC_Syntax_scope.

Notation "a :-> b" := (Fun a b)
    (at level 20, right associativity)  : STLC_Syntax_scope.

Notation "` x" := (Var x)
    (at level 1, no associativity)      : STLC_Syntax_scope.

Notation "\ x ~> t" := (Lam x t)
    (at level 90, right associativity)   : STLC_Syntax_scope.

Open Scope STLC_Syntax_scope.

