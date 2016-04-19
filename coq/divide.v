Require Import Arith. (* ring tactic *)

Definition divides (n m:nat) := exists p:nat, p*n = m.

Lemma divides_n_0 : forall n:nat, divides n 0.
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
  clear n. case m. intros n H. apply divides_n_0. clear m. intro m. intro n. 
  intro H. unfold divides in H. elim H. intros k. case k. simpl. intro H'.
  apply False_ind. rewrite <- plus_Snm_nSm in H'. simpl in H'. discriminate H'.
  clear k. intros k. simpl. intro H'. unfold divides. exists k.
  apply plus_reg_l with (p:=n). exact H'.
Qed.


