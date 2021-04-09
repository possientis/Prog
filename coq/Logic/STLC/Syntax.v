
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

Notation "e :: Ty" := (Ann e Ty)        : STLC_Syntax_scope.

Notation "e1 $ e2" := (App e1 e2)
    (at level 10, left associativity)   : STLC_Syntax_scope.

Notation "Ty :-> Ty'" := (Fun Ty Ty')
    (at level 20, right associativity)  : STLC_Syntax_scope.

Notation "` x" := (Var x)
    (at level 1, no associativity)      : STLC_Syntax_scope.

Notation "\ x ~> e" := (Lam x e)
    (at level 90, right associativity)   : STLC_Syntax_scope.

Open Scope STLC_Syntax_scope.

