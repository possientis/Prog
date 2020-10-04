Require Import List.

Require Import Logic.Class.Eq.

Require Import Logic.Nat.Eq.

Require Import Logic.Fol.Syntax.

Require Import Logic.Set.Set.
Require Import Logic.Set.Elem.

Require Import Logic.Lang1.Syntax.

(* Custom notations for predicates of 3 arguments appear to fail in Coq.        *)
(* Creating intermediary types Binding and Interpretation to bypass the issue.  *)
Inductive Binding : Type :=
| mkBind : forall (n:nat) (x:set), Binding
.

Notation "n ~> x" := (mkBind n x)
    (at level 1, no associativity) : Context_scope.

Inductive Context : Type :=
| O        : Context
| CtxSnoc  : Context -> Binding -> Context
.

Notation "G ';' x" := (CtxSnoc G x)
    (at level 50, left associativity) : Context_scope.

Open Scope Context_scope.

Inductive Find : Context -> Binding -> Prop :=
| FindZ : forall (G:Context) (n:nat) (x:set), Find (G ; n~>x) n~>x
| FindS : forall (G:Context) (n m:nat) (x y:set),
    n <> m      -> 
    Find G n~>x -> 
    Find (G ; m~>y) n~>x
.

Notation "G ':>' x" := (Find G x)
    (at level 60, no associativity) : Context_scope.

Open Scope Context_scope.

(* Just restating constructor FindZ with custom notations.                      *)
Lemma findZ : forall (G:Context) (n:nat) (x:set), G ; n~>x :> n~>x. 
Proof.
    intros G n x. constructor.
Qed.

(* Just restating constructor FindS with custom notations.                      *)
Lemma findS : forall (G:Context) (n m:nat) (x y:set),
    n <> m -> G :> n~>x -> G ; m~>y :> n~>x.
Proof.
    intros G n m x y H1 H2. constructor; assumption.
Qed.

(* Just so the predicate Eval can have two arguments instead of three.          *)
Inductive Interpretation : Type :=
| mkInterp : forall (p:Formula) (A:Prop), Interpretation
.

Notation "p ~ P" := (mkInterp p P)
    (at level 1, no associativity) : Context_scope.

Open Scope Context_scope.

Inductive Eval : Context -> Interpretation -> Prop :=
| EvalBot  : forall (G:Context), Eval G Bot ~ False
| EvalElem : forall (G:Context) (n m:nat) (x y:set),
    G :> n~>x -> G :> m~>y -> Eval G (Elem n m) ~ (x :: y)
| EvalImp  : forall (G:Context) (p1 p2:Formula) (A1 A2:Prop), 
    Eval G p1 ~ A1 -> Eval G p2 ~ A2 -> Eval G (Imp p1 p2) ~ (A1 -> A2)
|EvalAll   : forall (G:Context) (n:nat) (p1:Formula) (A1:set -> Prop),
    (forall (x:set), Eval (G ; n~>x) p1 ~ (A1 x)) ->
    Eval G (All n p1) ~ (forall (x:set), A1 x)
.

Notation "G :- I" := (Eval G I)
    (at level 60, no associativity).

Open Scope Context_scope.

(* Just restating constructor EvalBot with custom notations.                    *)
Lemma evalBot : forall (G:Context), G :- Bot ~ False.
Proof.
    intros G. constructor.
Qed.

(* Just restating constructor EvalElem with custom notations.                   *)
Lemma evalElem : forall (G:Context) (n m:nat) (x y:set),
    G :> n~>x -> G :> m~>y -> G :- (Elem n m) ~ (x :: y).
Proof.
    intros G n m x y H1 H2. constructor; assumption.
Qed.

(* Just restating constructor EvalImp with custom notations.                    *)
Lemma evalImp : forall (G:Context) (p1 p2:Formula) (A1 A2:Prop),
    G :- p1 ~ A1 -> G :- p2 ~ A2 -> G :- (Imp p1 p2) ~ (A1 -> A2).
Proof.
    intros G p1 p2 A1 A2 H1 H2. constructor; assumption.
Qed.

(* Just restating constructor EvalAll with custom notations.                    *)
Lemma evalAll : forall (G:Context) (n:nat) (p1:Formula) (A1:set -> Prop),
    (forall (x:set), G ; n~>x :- p1 ~ (A1 x)) -> 
        G :- (All n p1) ~ (forall (x:set), A1 x).
Proof.
    intros G n p1 A1 H1. constructor. assumption.
Qed.
