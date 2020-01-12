Require Import List.
Require Import Peano_dec.

Require Import Core.Fresh.

Inductive Formula : Type :=
| Bot  : Formula
| Elem : nat -> nat -> Formula
| Imp  : Formula -> Formula -> Formula
| All  : nat -> Formula -> Formula
.

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

Lemma checkFresh00 : fresh 0 0 = 1.
Proof. reflexivity. Qed.

Lemma checkFresh01 : fresh 0 1 = 2.
Proof. reflexivity. Qed.

Lemma checkFresh02 : fresh 0 2 = 1.
Proof. reflexivity. Qed.

Lemma checkFresh10 : fresh 1 0 = 2.
Proof. reflexivity. Qed.

Lemma checkFresh11 : fresh 1 1 = 0.
Proof. reflexivity. Qed.

Lemma checkFresh12 : fresh 1 2 = 0.
Proof. reflexivity. Qed.

Lemma checkFresh22 : fresh 2 2 = 0.
Proof. reflexivity. Qed.
