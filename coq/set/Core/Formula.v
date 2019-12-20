Inductive Formula : Type :=
| Bot  : Formula
| Elem : nat -> nat -> Formula
| Imp  : Formula -> Formula -> Formula
| All  : nat -> Formula -> Formula
.

Definition Not (p:Formula)   : Formula := Imp p Bot.
Definition Or  (p q:Formula) : Formula := Imp (Not p) q.
Definition And (p q:Formula) : Formula := Not (Or (Not p) (Not q)).


