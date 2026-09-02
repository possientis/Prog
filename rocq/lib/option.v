Lemma not_none_is_some : forall {A:Type} (o: option A),
  o <> None <-> exists x:A, o = Some x.
Proof.
  intros A o. split. elim o. intros a H. exists a. reflexivity.
  intro H. apply False_ind. apply H. reflexivity.
  intro H. elim H. intros x Hx. rewrite Hx. intros. discriminate.
Qed.

Lemma none_or_not_none : forall {A:Type} (o:option A),
  o = None \/ o <> None.
Proof.
  intros A o. elim o. intro a. right. intro H. discriminate.
  left. reflexivity.
Qed.




