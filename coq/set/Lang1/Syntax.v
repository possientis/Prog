Require Import List.
Require Import Peano_dec.

Require Import Utils.Fresh.

Inductive Formula : Type :=
| Bot  : Formula
| Elem : nat -> nat -> Formula
| Imp  : Formula -> Formula -> Formula
| All  : nat -> Formula -> Formula
.

Fixpoint free (p:Formula) : list nat :=
    match p with
    | Bot       => nil
    | Elem n m  => cons n (cons m nil)
    | Imp p q   => free p ++ free q
    | All n p   => remove (eq_nat_dec) n (free p)
    end.  

Definition Not (p:Formula)          :Formula := Imp p Bot.
Definition Or  (p q:Formula)        :Formula := Imp (Not p) q.
Definition And (p q:Formula)        :Formula := Not (Or (Not p) (Not q)).
Definition Exi  (n:nat) (p:Formula) :Formula := Not (All n (Not p)).
Definition Iff (p q:Formula)        :Formula := And (Imp p q) (Imp q p).

Definition Sub (n m:nat) : Formula := 
    let x := fresh n m in
        All x (Imp (Elem x n) (Elem x m)).

Definition Equ (n m:nat) : Formula := 
    let x := fresh n m in And
        (All x (Iff (Elem x n) (Elem x m)))
        (All x (Iff (Elem n x) (Elem m x))).

Definition Empty (n:nat) : Formula := 
    let x := fresh n n in
        All x (Not (Elem x n)).

(* Predicate expressing the 'minimality' of a set n in a set m                  *)
Definition Min (n m:nat) : Formula :=
    let x := fresh n m in And
        (Elem n m)
        (Not (Exi x (And (Elem x m) (Elem x n)))).


