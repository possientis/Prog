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


  Lemma id_P : P->P.
  Proof.
    intro H.
    assumption.
  Qed.

  Lemma id_PP : (P->P)->(P->P).
  Proof.
    intro H.
    intro Hp.
    assumption.
  Qed.

  Lemma imp_perm : (P->Q->R)->(Q->P->R).
  Proof.
    intro H.
    intro Hq.
    intro Hp.
    apply H.
    assumption.
    assumption.
  Qed.

  Lemma ignore_Q : (P->R)->P->Q->R.
  Proof.
    intro H.
    intro Hp.
    intro Hq.
    apply H.
    assumption.
  Qed.

  Lemma delta_imp : (P->P->Q)->P->Q.
  Proof.
    intro H.
    intro Hp.
    apply H.
    assumption.
    assumption.
  Qed.

  Lemma delta_impR : (P->Q)->(P->P->Q).
  Proof.
    intro H.
    intro Hp.
    assumption.
  Qed.

  Lemma diamond : (P->Q)->(P->R)->(Q->R->T)->P->T.
  Proof.
    intro Hpq.
    intro Hpr.
    intro H.
    intro Hp.
    apply H.
    apply Hpq.
    assumption.
    apply Hpr.
    assumption.
  Qed.

  Lemma weak_peirce : ((((P->Q)->P)->P)->Q)->Q.
  Proof.
    intro H.
    apply H.
    intro H'.
    apply H'.
    intro Hp.
    apply H.
    intro H''.
    assumption.
  Qed.






      
