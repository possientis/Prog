Require Import Le.

Require Import Logic.Class.Ord.

Require Import Logic.Nat.Leq.

Lemma leqDec : forall (n m:nat), { n <= m } + { ~ n <= m}.
Proof.
    induction n as [|n IH]; intros m.
    - left. apply le_0_n.
    - destruct m as [|m].
        + right. intros H1. apply le_0 in H1. inversion H1.
        + destruct (IH m) as [H1|H1].
            { left. apply le_n_S. assumption. }
            { right. intros H2. apply H1. apply le_S_n. assumption. }
Defined.

Lemma leqTotal : forall (n m:nat), n <= m \/ m <= n.
Proof.
    induction n as [|n IH]; intros m.
    - left. apply le_0_n.
    - destruct m as [|m].
        + right. apply le_0_n.
        + destruct (IH m) as [H1|H1].
            { left. apply le_n_S. assumption. }
            { right. apply le_n_S. assumption. }
Defined.

Instance OrdNat : Ord nat :=
    { leq       := le
    ; leqDec    := leqDec
    ; leqRefl   := le_refl
    ; leqTrans  := le_trans
    ; leqAsym   := le_antisym
    ; leqTotal  := leqTotal
    }. 
