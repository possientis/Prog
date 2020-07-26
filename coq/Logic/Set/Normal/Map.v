Require List.

Require Import Logic.Set.Set.
Require Import Logic.Set.Normal.InListOf.

Definition map (f:set -> set) (x:set) : set :=
    fromList (List.map f (toList x)).

Lemma mapCons : forall (f:set -> set) (x xs:set),
    map f (Cons x xs) = Cons (f x) (map f xs).
Proof.
    intros f x xs. unfold map. simpl. reflexivity.
Qed.

Lemma inListOfMapIff : forall (y xs:set) (f:set -> set),
    inListOf y (map f xs) <-> (exists (x:set), f x = y /\ inListOf x xs).
Proof.
    intros y xs f. unfold inListOf, map. rewrite toListFromList.
    apply List.in_map_iff.
Qed.
