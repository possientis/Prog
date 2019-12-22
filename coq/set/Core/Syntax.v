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
Definition Sub (m n:nat)            :Formula := All 0 (Imp (Elem 0 m) (Elem 0 n)).
Definition Equ (m n:nat)            :Formula := And
    (All 0 (Iff (Elem 0 m) (Elem 0 n)))
    (All 0 (Iff (Elem m 0) (Elem n 0))).


