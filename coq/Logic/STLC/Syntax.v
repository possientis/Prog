(* Type language where possible type variables are in type b.                   *)
(* The type 'b' may be thought of as the set of all possible 'type variables'.  *)
(* The type 'T b' may be thought of as the set of all type expressions.         *)
Inductive T (b:Type) : Type :=
| Base : b -> T b
| Fun  : T b -> T b -> T b
.

Arguments Base {b}.
Arguments Fun  {b}.

(* Function type                                                                *)
Notation "Ty :-> Ty'" := (Fun Ty Ty')
    (at level 20, right associativity)  : STLC_Syntax_scope.

(* Expression language for type variabled in b and variables in v.              *)  
(* The type 'v' may be thought of as the set of possible variables.             *)
(* The type 'Exp b v' may be thought of as the set of all expressions.          *)
Inductive Exp (b v:Type) : Type :=
| Ann : Exp b v -> T b -> Exp b v           (* Annotated expression             *)
| Var : v -> Exp b v                        (* Variable                         *)
| App : Exp b v -> Exp b v -> Exp b v       (* Application                      *)
| Lam : v -> Exp b v -> Exp b v             (* Lambda abstraction               *)
.

Arguments Ann {b} {v}.
Arguments Var {b} {v}.
Arguments App {b} {v}.
Arguments Lam {b} {v}.

(* Annotated expression                                                         *)
Notation "e :: Ty" := (Ann e Ty)        : STLC_Syntax_scope.

(* Variable                                                                     *)
Notation "` x" := (Var x)
    (at level 1, no associativity)      : STLC_Syntax_scope.

(* Application                                                                  *)
Notation "e1 $ e2" := (App e1 e2)
    (at level 10, left associativity)   : STLC_Syntax_scope.

(* Lambda abstraction                                                           *)
Notation "\ x ~> e" := (Lam x e)
    (at level 90, right associativity)   : STLC_Syntax_scope.

Open Scope STLC_Syntax_scope.
