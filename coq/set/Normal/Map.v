Require List.

Require Import Core.Set.

Definition map (f:set -> set) (x:set) : set :=
    fromList (List.map f (toList x)).

Lemma mapCons : forall (f:set -> set) (x xs:set),
    map f (Cons x xs) = Cons (f x) (map f xs).
Proof.
    intros f x xs. unfold map. simpl. reflexivity.
Qed.
