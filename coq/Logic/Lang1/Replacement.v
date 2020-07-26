Require Import List.

Require Import Logic.Axiom.LEM.

Require Import Logic.Set.Set.
Require Import Logic.Set.Elem.
Require Import Logic.Set.Incl.
Require Import Logic.Set.Equal.
Require Import Logic.Set.Compatible.

Require Import Logic.Lang1.Syntax.
Require Import Logic.Lang1.Semantics.
Require Import Logic.Lang1.Relevance.
Require Import Logic.Lang1.Environment.

Definition replacementF (P:Formula) (n m p q:nat) : Formula :=
    (Imp 
        (Elem n n) (* TODO *)
        (All n (Exi m (All p (Iff (Elem p m) (Exi q (And (Elem q n) P))))))).
