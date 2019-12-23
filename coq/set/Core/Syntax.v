Require Import List.

Require Import Core.Nat.

Inductive Formula : Type :=
| Bot  : Formula
| Elem : nat -> nat -> Formula
| Imp  : Formula -> Formula -> Formula
| All  : nat -> Formula -> Formula
.

Fixpoint fresh (m:nat) (n:nat) : nat :=
    match eq_nat_dec 0 m, eq_nat_dec 0 n with
    | right _, right _  => 0 
    | left  _, left  _  => 1
    | left  _, right _  =>          (* m = 0 so cannot use 0 *)
        match eq_nat_dec 1 n with
        | left  _       => 2        (* n = 1 so cannot use 1 *)
        | right _       => 1 
        end
    | right _, left  _  =>          (* n = 0 so cannot use 0 *) 
        match eq_nat_dec 1 m with
        | left  _       => 2        (* m = 1 so cannot use 1 *)
        | right _       => 1      
        end
    end.

Definition Not (p:Formula)          :Formula := Imp p Bot.
Definition Or  (p q:Formula)        :Formula := Imp (Not p) q.
Definition And (p q:Formula)        :Formula := Not (Or (Not p) (Not q)).
Definition Exi  (n:nat) (p:Formula) :Formula := Not (All n (Not p)).
Definition Iff (p q:Formula)        :Formula := And (Imp p q) (Imp q p).

Definition Sub (m n:nat) : Formula := 
    let x := fresh m n in
        All x (Imp (Elem x m) (Elem x n)).

Definition Equ (m n:nat) : Formula := 
    let x := fresh m n in And
        (All x (Iff (Elem x m) (Elem x n)))
        (All x (Iff (Elem m x) (Elem n x))).

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

