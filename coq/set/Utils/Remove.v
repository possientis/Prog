Require Import List.
Require Import Peano_dec.

Lemma removeStill : forall (n m:nat) (xs:list nat),
    n <> m -> In m xs -> In m (remove eq_nat_dec n xs).
Proof.
    intros n m xs. induction xs as [|x xs IH].
    - intros _ H. inversion H.
    - intros Hnm H. simpl. destruct (eq_nat_dec n x) eqn:E. 
        + apply IH.
            { assumption. }
            { destruct H as [H1|H2]. 
                { exfalso. apply Hnm. rewrite <- H1. assumption. }
                { assumption. }
            }
        + destruct H.  
            { left. assumption. }
            { right. apply IH; assumption. }
Qed.


