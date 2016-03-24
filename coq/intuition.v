Theorem T1 : forall A:Prop, ~~(A\/~A).
Proof.
  intros A H. cut(~A). intro notA. cut (~A-> False). intro nnotA.
  apply nnotA. exact notA. intro. elim H. right. exact notA.
  intro. apply H. left. assumption.
Qed.
