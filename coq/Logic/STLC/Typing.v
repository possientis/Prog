Require Import Logic.Class.Eq.

Require Import Logic.STLC.Valid.
Require Import Logic.STLC.Syntax.
Require Import Logic.STLC.IsType.
Require Import Logic.STLC.Context.

(* Just so the predicate Judgment can have two arguments instead of three.      *)
Inductive Typing (b v:Type) : Type :=
| mkTyping : forall (e:Exp b v) (Ty:T b), Typing b v
.

Arguments Typing   {b} {v}.
Arguments mkTyping {b} {v}.

Notation "e >: Ty" :=(mkTyping e Ty)
    (at level 25, no associativity)      : STLC_Typing_scope.

Open Scope STLC_Typing_scope.

Inductive Judgement (b v:Type) (eq:Eq v): @Context b v -> @Typing b v  -> Prop :=
| JAnn : forall (G:Context) (e:Exp b v) (Ty:T b),
    Valid G                                 ->  (* G is a valid context         *)
    G :- Ty                                 ->  (* Ty well-formed expression    *)
    Judgement b v eq G (e >: Ty)            ->  (* e is of type Ty in context G *) 
    Judgement b v eq G ((e :: Ty) >: Ty)        (* Annotated expr same type     *)
| JVar : forall (G:Context) (x:v) (Ty:T b),
    Valid G                                 ->  (* G is a valid context         *)
    G :>> x ::: Ty                          ->  (* variable x declared type Ty  *) 
    Judgement b v eq G (`x >: Ty)               (* variable expr same type      *) 
| JApp : forall (G:Context) (e1 e2:Exp b v) (Ty Ty':T b),
    Valid G                                 ->  (* G is a valid context         *)
    Judgement b v eq G (e1 >: Ty :-> Ty')   ->  (* e1 of type Ty :-> Ty'        *)
    Judgement b v eq G (e2 >: Ty)           ->  (* e2 of type Ty                *)
    Judgement b v eq G (e1 $ e2 >: Ty')         (* e1 e2 of type Ty'            *)
.
