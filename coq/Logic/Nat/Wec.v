Require Import Le.
Import Nat.

Require Import Logic.Class.Eq.
Require Import Logic.Class.Ord.

Require Import Logic.Axiom.Wec.

Require Import Logic.Nat.Leq.
Require Import Logic.Nat.Ord.

Lemma boundedWec : forall (p:nat -> Prop), pWec p -> 
    forall (n:nat), Wec (exists (m:nat), p m /\ m <= n).
Proof.
    intros p H1. induction n as [|n IH].
    - destruct (H1 0) as [H2|H2].
        + left. exists 0. split; try assumption. apply le_n.
        + right. intros [m [H3 H4]]. apply le_0 in H4. subst.
          apply H2 in H3. contradiction.
    - destruct IH as [H2|H2].
        + destruct H2 as [m [H2 H3]].
          left. exists m. split; try assumption. apply le_S. assumption.
        + destruct (H1 (S n)) as [H3|H3].
            { left. exists (S n). split; try assumption. apply le_n. }
            { right. intros [m [H4 H5]].   
              destruct (leqDec m n) as [H6|H6].
                { apply H2. exists m. split; assumption. }
                { assert (m = S n) as H7. 
                    { apply le_antisymm; try assumption. 
                      apply not_le_ge. assumption. }
                  subst. apply H3 in H4. contradiction. }}
Defined.
