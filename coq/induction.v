Lemma plus_n_O : forall n:nat, n = n + 0.
  intro n.
  elim n.
  simpl.
  reflexivity.
  simpl.
  auto.
Qed.

Hint Resolve plus_n_O.

Lemma plus_n_S : forall n m:nat, S(n + m) = n + (S m).
  induction n; simpl; auto.
Qed.

Hint Resolve plus_n_S.

Lemma plus_com : forall n m:nat, n + m = m + n.
  simple induction m; simpl; auto.
  intros m' E; rewrite <- E; auto.
Qed.

