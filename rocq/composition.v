Set Implicit Arguments.

Definition compose : forall A B C:Type, (A->B)->(B->C)->A->C :=
    (fun A B C f g x => g (f x)).

Print compose.
Theorem compose_assoc: forall (A B C D:Type)(f: A->B)(g:B->C)(h:C->D),
  compose f (compose g h) = compose (compose f g) h.
Proof.
  intros A B C D f g h.
  reflexivity.
Qed.
