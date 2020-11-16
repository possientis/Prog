Require Import Le.

Require Import Logic.Class.Eq.
Require Import Logic.Class.Ord.

Require Import Logic.Axiom.Dec.

Require Import Logic.Nat.Leq.
Require Import Logic.Nat.Ord.


Lemma boundedDec : forall (p:nat -> Prop), pDec p -> 
    forall (n:nat), Dec (exists (m:nat), p m /\ m <= n).
Proof.
    intros p H1. induction n as [|n IH].
    - destruct (H1 0) as [H2|H2].
        + left. exists 0. split; try assumption. apply le_n.
        + right. intros [m [H3 H4]]. apply le_0 in H4. subst.
          apply H2 in H3. contradiction.
    - destruct IH as [H2|H2].
          (* destruct of exists statement ok as goal in Prop after 'left'       *)
        + left. destruct H2 as [m [H2 H3]]. exists m. split; try assumption.
          apply le_trans with n; try assumption. apply le_S, le_n.
        + destruct (H1 (S n)) as [H3|H3].
            { left. exists (S n). split; try assumption. apply le_n. }
            (* destruct of exists statement ok as goal in Prop after 'right'    *)
            { right. intros H4. destruct H4 as [m [H4 H5]].
              destruct (eqDec m (S n)) as [H6|H6].
                { subst. apply H3 in H4. contradiction. }
                { apply H2. exists m. split; try assumption.
                    destruct (leqDec m n) as [H7|H7].
                    { assumption. }
                    { apply not_le_ge in H7. exfalso. apply H6.
                      apply le_antisym; assumption. }}}
Defined.
