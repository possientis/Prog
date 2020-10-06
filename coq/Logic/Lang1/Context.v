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

Definition inclCtx (G H:Context) : Prop :=
    forall (n:nat) (x:set), G :> n~>x -> H :> n~>x.

Notation "G <= H"  := (inclCtx G H)
    (at level 70, no associativity) : Context_scope.

Open Scope Context_scope.

(*
Lemma inclCtxExtend : forall (G H:Context) (n:nat) (x:set),
    G <= H -> G ; n~>x <= H ; n~>x.
Proof.
    intros G H n x. unfold inclCtx. intros H2 m y H3.
    remember (G ; n~>x) as G' eqn:G1. remember (H ; n~>x) as H' eqn:H1. 
    revert G1 H1.
    
Show.
*)
