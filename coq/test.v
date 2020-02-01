Lemma L1 : forall (A B:Prop), A \/ B -> ~A -> B.
Proof.
    intros A B [H|H] H'.
    - apply H' in H. contradiction.
    - assumption.
Qed.
