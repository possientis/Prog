Lemma simpl_pattern_example: 3*3 + 3*3 = 18.
Proof.
  simpl (3*3) at 2.
  simpl. reflexivity.
Qed.

Lemma lazy_example: forall n:nat, (S n) + 0 = S n.
Proof.
  intros n. lazy beta iota zeta delta. fold plus. (* 'fix plus ... ' so fold works *)
  auto.
Qed.
