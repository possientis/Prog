Definition Is_S (n:nat) :=
  match n with 
  | O   => False
  | S p => True
  end.

Lemma S_Is_S : forall n:nat, Is_S(S n).
  intro n.
  simpl.
  trivial.
Qed.

Lemma no_confusion : forall n:nat, 0 <> S n.
  red.
  intro n.
  intro H.
  change (Is_S 0).
  rewrite H.
  apply S_Is_S.
  Restart.
  intro n.
  discriminate.
Qed.

Inductive le (n:nat) : nat -> Prop :=
  | le_n : le n n
  | le_S : forall m:nat, le n m -> le n (S m).

Lemma le_n_S : forall n m:nat, le n m -> le (S n) (S m).
  intros n m n_le_m.
  elim n_le_m.
  apply le_n.
  intros.
  apply le_S.
  assumption.
  Restart.
  Hint Resolve le_n le_S.
  simple induction 1; auto.
Qed.

Lemma tricky : forall n:nat, le n 0 -> n = 0.
  intros n H.
  inversion_clear H.
  reflexivity.
Qed.

