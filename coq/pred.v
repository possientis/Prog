Definition pred: forall n:nat, {p:nat | n = S p}+{n = 0}.
  intros n. case n.
  right. reflexivity.
  intros p. left. exists p. reflexivity.
Defined.

Definition pred_partial: forall n:nat, n <> 0 -> nat.
  intros n. case n. intros H. elim H. reflexivity. (* don't get this *)
  intros p H'. exact p.
Defined.
