Inductive even : nat -> Prop :=
  | Even0 : even 0
  | EvenS : forall n:nat, even n -> even (S (S n)).

Lemma not_1_even: ~ even 1.
Proof.
  unfold not. cut (forall n:nat, n = 1 -> even n -> False). eauto.
  intros n H He. generalize H. clear H. generalize He. elim He.
  intros. discriminate. clear He n. intros. discriminate.
Qed.


Lemma not_1_even': ~ even 1.
Proof.
  unfold not. intros H. inversion H.
Qed.

Lemma plus_2_even_inv: forall n:nat, even (S (S n)) -> even n.
Proof.
  intros n H. inversion H. exact H1.
Qed.


Lemma not_1_even'': ~ even 1.
Proof.
  intro H. generalize (refl_equal 1).
  pattern 1 at -2. elim H; intros; discriminate.
Qed.


Lemma plus_2_even_inv': forall n:nat, even (S (S n)) -> even n.
Proof.
  intro n. cut(forall m:nat, m = S (S n) -> even m -> even n).
  eauto. intros m H He. generalize He H. clear H. generalize n.
  clear n. elim He. intros. discriminate. clear m He.
  intros. injection H1. intros. rewrite <- H2. exact H.
Qed.

