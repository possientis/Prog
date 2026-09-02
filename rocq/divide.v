Require Import Arith. (* ring tactic *)
Require Import Notations.
Require Import Datatypes.
Require Import Logic.

Open Scope nat_scope.


Definition divides (n m:nat) := exists p:nat, p*n = m.

Lemma divides_0 : forall n:nat, divides n 0.
Proof.
  intro n. unfold divides. exists 0. auto.
Qed.


Lemma divides_plus : forall n m:nat, divides n m -> divides n (n + m).
Proof.
  intros n m. unfold divides. intro H. elim H. intros k H'. exists (S k).
  rewrite <- H'. ring.
Qed.

Lemma not_divides_plus : forall n m:nat, ~divides n m -> ~divides n (n+m).
Proof.
  intros n m H H'. apply H. generalize H'. generalize n. clear H'. clear H. 
  clear n. case m. intros n H. apply divides_0. clear m. intro m. intro n. 
  intro H. unfold divides in H. elim H. intros k. case k. simpl. intro H'.
  apply False_ind. rewrite <- plus_Snm_nSm in H'. simpl in H'. discriminate H'.
  clear k. intros k. simpl. intro H'. unfold divides. exists k.
  apply plus_reg_l with (p:=n). exact H'.
Qed.

Lemma not_divides_lt : forall n m:nat, 0 < m -> m < n -> ~divides n m.
Proof.
  intros n m H0 Hn H. unfold divides in H. elim H. intros p Hp. generalize H0 Hn Hp.
  case p. simpl. clear H0. intro H0. clear Hn. intro Hn. unfold lt in H0. intro H'.
  rewrite <- H' in H0. cut(0 = 1). intro H''. discriminate H''. apply le_n_0_eq.
  exact H0. intro q. clear H0. intro H0. clear Hn. intro Hn. intro H'. simpl in H'.
  cut (n <= m). intro H''. apply le_not_lt with (n:=n)(m:=m). exact H''. exact Hn.
  rewrite <- H'. apply le_plus_l.
Qed.

Lemma not_lt_2_divides : forall n m:nat, n <> 1 -> n < 2 -> 0 < m -> ~divides n m.
Proof.
  intros n m H1 H2 Hm. unfold divides. intro H. elim H. intros p Hp. cut(n=0).
  intro H'. rewrite H' in Hp. rewrite mult_0_r in Hp. unfold lt in Hm. 
  rewrite <- Hp in Hm. cut (0 = 1). intro H''. discriminate H''. apply le_n_0_eq.
  exact Hm. generalize H1 H2. case n. tauto. intro q. simpl. clear H1 H2.
  intros H1 H2. apply False_ind. unfold lt in H2. apply H1. simpl. apply False_ind.
  generalize H1 H2. case q. tauto. intro r. intro H3. clear H3 H2 H1 Hp H Hm n m p q.
  intro H. cut (S r = 0). intro H'. discriminate H'. symmetry. apply le_n_0_eq.
  apply le_S_n. apply le_S_n. exact H.
Qed.

Lemma le_plus_minus: forall n m:nat, le n m -> m = n + (m - n).
Proof.
  intros n m. elim m. intro H. cut (0 = n). intro H'. rewrite <- H'. simpl. 
  reflexivity. apply le_n_0_eq. exact H. clear m. intros m IH H.
  cut ((n < S m)\/(n = S m)). intro H'. elim H'. unfold lt. intro H''.
  rewrite <- minus_Sn_m. rewrite <- plus_Snm_nSm. unfold plus. fold plus.
  rewrite <- IH. reflexivity. apply le_S_n. exact H''. apply le_S_n.
  exact H''. intro H''. rewrite <- H''. rewrite <- minus_diag_reverse. ring.
  apply le_lt_or_eq. exact H.
Qed.

Lemma lt_lt_or_eq: forall n m:nat, n < S m -> n < m \/ n = m.
Proof.
  intro n. elim n. intros m H. clear H. case m. right. reflexivity.
  clear m. intro m. left. auto with arith. clear n. intros n IH m.
  case m. intro H. unfold lt in H. right. symmetry. apply le_n_0_eq.
  apply le_S_n. exact H. clear m. intros m H. cut (n < m \/ n = m).
  intro H'. elim H'. intro Hnm. left. auto with arith. intro Hnm.
  right. auto with arith. apply IH. auto with arith.
Qed.



