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

  Definition f: (nat->bool)->(nat->bool)->(nat->bool).
    intros f1 f2.
    assumption.
  Defined.

  Print f.
  Eval compute in (f (fun n => true) (fun n => false) 45).

  Opaque f.

  Eval compute in (f (fun n => true) (fun n => false) 45).

  Lemma triple_imp_try : (((P->Q)->Q)->Q)->P->Q.
  Proof.
    intro H.
    intro Hp.
    apply H.
    intro Hpq.
    apply Hpq.
    assumption.
  Qed.

  Section proof_of_triple_impl.
    Hypothesis H : ((P->Q)->Q)->Q.
    Hypothesis p : P.

    Lemma Rem : (P->Q)->Q. 
    Proof (fun H0:P->Q => H0 p).

    Lemma triple_impl : Q.
    Proof H Rem.
 End proof_of_triple_impl.

 Print triple_impl.
 Print Rem.

  Theorem then_example: P->Q->(P->Q->R)->R.
  Proof.
    intros p q H.
    apply H; assumption.
  Qed.

  Theorem triple_impl_one_shot : (((P->Q)->Q)->Q)->P->Q.
  Proof.
    intros H p; apply H; intro H0; apply H0; assumption.
  Qed.

  Theorem compose_example : (P->Q->R)->(P->Q)->(P->R).
  Proof.
    intros H H0 p; apply H; [assumption | apply H0; assumption].
  Qed.




      
