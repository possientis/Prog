Require Import List.

Require Import Logic.Class.Eq.

Require Import Logic.Nat.Eq.

Require Import Logic.Fol.Syntax.

Require Import Logic.Set.Set.
Require Import Logic.Set.Elem.

Require Import Logic.Lang1.Syntax.

Definition Context : Type := list (nat * set).

Inductive Find : Context -> nat -> set -> Prop :=
| FindZ : forall (G:Context) (n:nat) (x:set), Find (cons (n,x) G) n x
| FindS : forall (G:Context) (n m:nat) (x y:set),
    n <> m     -> 
    Find G n x -> 
    Find (cons (m,y) G) n x
.

Inductive Eval : Context -> Formula -> Prop -> Prop :=
| EvalBot  : forall (G:Context), Eval G Bot False
| EvalElem : forall (G:Context) (n m:nat) (x y:set),
    Find G n x -> Find G m y -> Eval G (Elem n m) (x :: y)
| EvalImp  : forall (G:Context) (p1 p2:Formula) (P1 P2:Prop), 
    Eval G p1 P1 -> Eval G p2 P2 -> Eval G (Imp p1 p2) (P1 -> P2)
|EvalAll   : forall (G:Context) (n:nat) (p1:Formula) (P1:set -> Prop),
    (forall (x:set), Eval (cons (n,x) G) p1 (P1 x)) ->
    Eval G (All n p1) (forall (x:set), P1 x)
.



