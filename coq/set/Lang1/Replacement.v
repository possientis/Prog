Require Import List.

Require Import Utils.LEM.

Require Import Core.Set.
Require Import Core.Elem.
Require Import Core.Incl.
Require Import Core.Equal.
Require Import Core.Compatible.

Require Import Lang1.Syntax.
Require Import Lang1.Semantics.
Require Import Lang1.Relevance.
Require Import Lang1.Environment.

Definition replacementF (P:Formula) (n m p q:nat) : Formula :=
    (Imp 
        (Elem n n) (* TODO *)
        (All n (Exi m (All p (Iff (Elem p m) (Exi q (And (Elem q n) P))))))).
