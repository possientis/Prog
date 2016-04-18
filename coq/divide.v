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
  intros n m. unfold divides. intros H H'. elim H'. intros k H''.
  apply H. cut (exists p, k = S p). intro Hk. elim Hk. intros p Hp. 
  exists p. apply plus_reg_l with (p:=n). rewrite <- H''. rewrite Hp.
  auto with arith.
