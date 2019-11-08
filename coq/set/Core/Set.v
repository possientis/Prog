(* 'Set' appears to be a Coq keyword, so lowercase it                           *)
Inductive set : Type :=
| Nil   : set
| Cons  : set -> set -> set
.

Fixpoint toList (x:set) : list set :=
    match x with
    | Nil           => nil
    | (Cons x xs)   => cons x (toList xs)
    end.

Fixpoint fromList (xs:list set) : set :=
    match xs with
    | nil           => Nil
    | cons x xs     => Cons x (fromList xs)
    end.


Lemma fromListToList : forall (xs:set), fromList (toList xs) = xs.
Proof.
    induction xs as [|x _ xs IH].
    - reflexivity. 
    - simpl. rewrite IH. reflexivity.
Qed.

Lemma toListFromList : forall (xs:list set), toList (fromList xs) = xs.
Proof.
    induction xs as [|x xs IH].
    - reflexivity.
    - simpl. rewrite IH. reflexivity.
Qed.




