Definition eq_dec (A:Type) :=
  forall x y:A, {x = y} + {x <> y}.

Lemma nat_dec : eq_dec nat.
Proof.
  unfold eq_dec. intros x. elim x.
  clear x. intro y. elim y.
  clear y. auto.
  clear y. intros. right. auto.
  clear x. intros n IH m. elim m.
  clear m. intros. right. auto.
  clear m. intros m H. clear H.
  elim (IH m).
  intro H. rewrite H. left. reflexivity.
  intro H. right. intro H'. apply H. injection H'. auto.
Qed.


