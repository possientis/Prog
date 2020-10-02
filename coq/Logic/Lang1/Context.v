Require Import List.

Require Import Logic.Class.Eq.

Require Import Logic.Nat.Eq.

Require Import Logic.Fol.Syntax.

Require Import Logic.Set.Set.
Require Import Logic.Set.Elem.

Require Import Logic.Lang1.Syntax.

Inductive Context : Type :=
| O        : Context
| CtxSnoc  : Context -> (nat * set) -> Context
.

Notation "G ';' x" := (CtxSnoc G x)
    (at level 50, left associativity) : Context_scope.

Open Scope Context_scope.

Inductive Find : Context -> (nat * set) -> Prop :=
| FindZ : forall (G:Context) (n:nat) (x:set), Find (G ; (n,x)) (n,x)
| FindS : forall (G:Context) (n m:nat) (x y:set),
    n <> m       -> 
    Find G (n,x) -> 
    Find (G ; (m,y)) (n,x)
.

Notation "G ':>' x" := (Find G x)
    (at level 60, no associativity) : Context_scope.

Open Scope Context_scope.

(* Just restating constructor FindZ with custom notations.                      *)
Lemma findZ : forall (G:Context) (n:nat) (x:set), G ; (n,x) :> (n,x). 
Proof.
    intros G n x. constructor.
Qed.

(* Just restating constructor FindS with custom notations.                      *)
Lemma findS : forall (G:Context) (n m:nat) (x y:set),
    n <> m -> G :> (n,x) -> G ; (m,y) :> (n,x).
Proof.
    intros G n m x y H1 H2. constructor; assumption.
Qed.

Inductive Eval : Context -> Formula -> Prop -> Prop :=
| EvalBot  : forall (G:Context), Eval G Bot False
| EvalElem : forall (G:Context) (n m:nat) (x y:set),
    G :> (n,x) -> G :> (m,y) -> Eval G (Elem n m) (x :: y)
| EvalImp  : forall (G:Context) (p1 p2:Formula) (P1 P2:Prop), 
    Eval G p1 P1 -> Eval G p2 P2 -> Eval G (Imp p1 p2) (P1 -> P2)
|EvalAll   : forall (G:Context) (n:nat) (p1:Formula) (P1:set -> Prop),
    (forall (x:set), Eval (G ; (n,x)) p1 (P1 x)) ->
    Eval G (All n p1) (forall (x:set), P1 x)
.



