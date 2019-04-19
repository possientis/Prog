Inductive Id (X:Set) : X -> X -> Prop :=
| refl : forall (x:X), Id X x x
.

Arguments Id {X} _ _.
Arguments refl {X} _.

Notation "x == y" := (Id x y) (at level 70, no associativity).

Lemma unit_singleton : forall (x:unit), x = tt.
Proof. intros []. reflexivity. Qed.

(*
Lemma Id_singleton : forall (X:Set) (x y:X) (p q: x == y), p = q.
Proof.
    intros X x y p q. destruct p.

Show.
*)



