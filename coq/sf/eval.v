Require Import bool.
Require Import nat.
Require Import syntax.
Require Import state.
Require Import dictionary.


Fixpoint aeval (env:State) (a:aexp) : nat :=
    match a with
    | ANum n        => n
    | AKey k        => env k
    | APlus a1 a2   => (aeval env a1) + (aeval env a2)
    | AMinus a1 a2  => (aeval env a1) - (aeval env a2)
    | AMult a1 a2   => (aeval env a1) * (aeval env a2) 
    end.


Fixpoint beval (env:State) (b:bexp) : bool :=
    match b with
    | BTrue         => true
    | BFalse        => false
    | BEq a1 a2     => eqb (aeval env a1) (aeval env a2)
    | BLe a1 a2     => leb (aeval env a1) (aeval env a2)
    | BNot b1       => negb (beval env b1)
    | BAnd b1 b2    => andb (beval env b1) (beval env b2)
    end.

Fixpoint ceval_fun_no_while (env:State) (c:com) : State :=
    match c with
    | SKIP                      => env
    | x ::= a1                  => t_update env x (aeval env a1)
    | c1 ;; c2                  => let env' := ceval_fun_no_while env c1 
                                   in ceval_fun_no_while env' c2
    | IFB b THEN c1 ELSE c2 FI  => if (beval env b)
                                   then ceval_fun_no_while env c1
                                   else ceval_fun_no_while env c2 
    | WHILE b DO c END          => env
    end.


Inductive ceval : com -> State -> State -> Prop :=
| E_Skip     : forall e, ceval SKIP e e
| E_Ass      : forall e a n x, aeval e a = n -> ceval (x ::= a) e (t_update e x n)
| E_Seq      : forall e e' e'' c1 c2, ceval c1 e e' -> ceval c2 e' e'' ->
                ceval (c1 ;; c2) e e''
| E_IfTrue   : forall e e' b c1 c2, beval e b = true -> ceval c1 e e' ->
                ceval (IFB b THEN c1 ELSE c2 FI) e e'
| E_IfFalse  : forall e e' b c1 c2, beval e b = false -> ceval c2 e e' ->
                ceval (IFB b THEN c1 ELSE c2 FI) e e'
| E_WhileEnd : forall e b c, beval e b = false -> ceval (WHILE b DO c END) e e
| E_WhileLoop: forall e e' e'' b c, beval e b = true -> ceval c e e' ->
                ceval (WHILE b DO c END) e' e'' -> 
                ceval (WHILE b DO c END) e  e''
.
