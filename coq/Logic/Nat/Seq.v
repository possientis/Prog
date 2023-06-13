Require Import Le.
Require Import Plus.
Import Nat.

Require Import Logic.Nat.Leq.

Lemma noDecreasingSeq : ~ exists (f:nat -> nat), forall (n:nat), f (S n) < f n.
Proof.
    intros [f H]. 
    assert (forall (n:nat), n + f n <= f 0) as H'.
        { induction n as [|n IH].
            - apply le_n.
            - apply le_trans with (n + f n).
                + simpl. apply add_lt_mono_l. apply H.
                + apply IH. }
    assert (S (f 0) <= f 0) as C.
        { apply le_trans with (S (f 0) + f (S (f 0))).
            - apply le_add_r.
            - apply H'. }
    apply not_le_Sn_n with (f 0). assumption.    
Qed.
