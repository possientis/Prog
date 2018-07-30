Lemma neq_sym : forall (v:Type) (x y:v), x <> y -> y <> x.
Proof.
    intros v x y H H'. apply H. symmetry. assumption.
Qed.

