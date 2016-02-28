Section Minimal_propositional_logic.
  Variables P Q R T : Prop.
  
  Theorem imp_trans : (P->Q)->(Q->R)->P->R.
  Proof. (* optional *)
    intros H H' p.
    apply H'.
    apply H.
    assumption.
  Qed.
  Section example_of_assumption.
    Hypothesis H: P->Q->R.
    (*Variable  H': P->Q->R.*)
    Lemma L1 : P->Q->R.
    Proof.
      assumption.
    Qed.
  End example_of_assumption.

  Theorem delta : (P->P->Q)->P->Q.
  Proof.
    exact (fun (H:P->P->Q) (p:P) => H p p).
  Qed.

  Theorem beta : (P->P->Q)->P->Q.
  Proof (fun H p => H p p).

  Theorem apply_example : (Q->R->T)->(P->Q)->P->R->T.
  Proof.
    intros H H0 p.
    apply H.
    exact (H0 p).
  Qed.

  Theorem imp_dist : (P->Q->R)->(P->Q)->(P->R).
  Proof.
    intros H H' p.
    apply H.
    assumption.
    apply H'.
    assumption.
  Qed.






      
