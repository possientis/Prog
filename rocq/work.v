Lemma L1: forall P: Prop, P->P.
Proof.
  intro P.
  intro H.
  exact H. 
Qed.

Lemma L2: forall P Q R: Prop, (P->Q)->(Q->R)->(P->R).
Proof.
  intros P Q R.
  intro Hpq.
  intro Hqr.
  intro Hp.
  apply Hqr.
  apply Hpq.
  apply Hp.
Qed.

Lemma L3: forall P Q R S: Prop, (P->Q)->(P->R)->(Q->R->S)->(P->S).
Proof.
  intros P Q R S.
  intro Hpq.
  intro Hpr.
  intro H.
  intro Hp.
  apply H.
  apply Hpq.
  exact Hp.
  apply Hpr.
  exact Hp.
Qed.

Lemma L4: forall P Q R: Prop, (P->Q->R)->(Q->P->R).
Proof.
  intros P Q R.
  intro H.
  intro Hq.
  intro Hp.
  apply H.
  exact Hp.
  exact Hq.
Qed.

Lemma L5: forall P Q R: Prop, (P->Q->R)->(P->Q)->(P->R).
Proof.
  intros P Q R.
  intro H.
  intro Hpq.
  intro Hp.
  apply H.
  exact Hp.
  apply Hpq.
  exact Hp.
Qed.

Lemma L6: forall P Q: Prop, ((((P->Q)->P)->P)->Q)->Q.
Proof.
  intros P Q.
  intro H.
  apply H.
  intro H'.
  apply H'.
  intro Hp.
  apply H.
  intro H''.
  exact Hp.
Qed.

Lemma L7: forall P Q: Prop, P->Q->P/\Q.
Proof. 
  apply conj.
Qed.

Lemma and_elim_left: forall P Q: Prop, P/\Q -> Q.
Proof.
  intros P Q.
  apply and_ind.
  intro Hp.
  intro Hq.
  exact Hq.
Qed.


Lemma and_elim_right: forall P Q: Prop, P/\Q -> P.
Proof.
  intros P Q.
  apply and_ind.
  intro Hp.
  intro Hq.
  exact Hp.
Qed.

Lemma L8 : forall P Q R : Prop, P->Q->R->P/\Q/\R.
Proof.
  intros P Q R.
  intros Hp Hq Hr.
  apply conj.
  exact Hp.
  apply conj.
  exact Hq.
  exact Hr.
Qed.

Lemma L9 : forall A B: Prop, A/\B -> B/\A.
Proof.
  intros A B.
  apply and_ind.
  intros Ha Hb.
  apply conj.
  exact Hb.
  exact Ha.
Qed.

Lemma L10: forall A B C: Prop, ((A/\B)/\C -> A/\(B/\C)) /\ ((A/\(B/\C) -> (A/\B)/\C)).
Proof.
  intros A B C.
  apply conj.
  intro H.
  apply conj.
  destruct H.
  destruct H.
  exact H.
  apply conj.
  destruct H.
  destruct H.
  exact H1.
  destruct H.
  exact H0.
  intro H.
  apply conj.
  apply conj.
  destruct H.
  exact H.
  destruct H.
  destruct H0.
  exact H0.
  destruct H.
  destruct H0.
  exact H1.
Qed.


