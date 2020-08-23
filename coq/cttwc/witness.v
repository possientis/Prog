Inductive Sig (a:Type) (p:a -> Type) : Type :=
| Ex : forall (x:a), p x -> Sig a p
.

Arguments Sig {a}.
Arguments Ex {a} {p}.


(* Elim restriction, cant do the obvious.                                       *)
Definition witness : forall (f:nat -> bool),
    (exists (n:nat), f n = true) -> Sig (fun n => f n = true).
Proof.
Admitted.
