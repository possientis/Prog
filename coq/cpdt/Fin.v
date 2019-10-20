Inductive Fin : nat -> Set :=
| First : forall (n:nat), Fin (S n)
| Next  : forall (n:nat), Fin n -> Fin (S n)
.

Arguments Next {n}.

Definition x2 : Fin 3 := First 2.
Definition x1 : Fin 3 := Next (First 1).
Definition x0 : Fin 3 := Next (Next (First 0)).
