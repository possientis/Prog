Variable A:Type.
Variable B:Type.

Definition C:Type := A->B.
Definition D:Type := forall (x:A), B.

Proposition same : C = D.
Proof.
  unfold C. unfold D. reflexivity.
Qed.


