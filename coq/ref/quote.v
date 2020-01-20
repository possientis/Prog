Require Import Quote.

Parameters A B C : Prop.

Inductive Formula : Type :=
| fAnd : Formula -> Formula -> Formula
| fOr  : Formula -> Formula -> Formula
| fNot : Formula -> Formula
| fTrue: Formula
| fCon : Prop -> Formula    (* Constructor for constants *)
.


Fixpoint eval (p:Formula) : Prop :=
    match p with
    | fAnd p1 p2    => eval p1 /\ eval p2
    | fOr  p1 p2    => eval p1 \/ eval p2
    | fNot p1       => ~ eval p1
    | fTrue         => True
    | fCon c        => c
    end.


Lemma L1 : A /\ (A /\ True) /\ ~B /\ (A <-> A).
Proof.
    quote eval.

Show.




