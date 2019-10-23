(* 'Set' appears to be a Coq keyword, so lowercase it is                        *)
Inductive set : Type :=
| Nil   : set
| Cons  : set -> set -> set
.

Fixpoint toList (x:set) : list set :=
    match x with
    | Nil           => nil
    | (Cons x xs)   => cons x (toList xs)
    end.

Lemma set_eq_dec : forall (x y:set), {x = y} + {x <> y}.
Proof.
    intros xs. induction xs as [|x IH1 xs IH2]; intros ys.
    - destruct ys as [|y ys].
        + left. reflexivity.
        + right. intros H. inversion H.
    - destruct ys as [|y ys].
        + right. intros H. inversion H.
        + destruct (IH1 y) as [H1|H1].
            { subst. destruct (IH2 ys) as [H2|H2].
                { subst. left. reflexivity. }
                { right. intros H. inversion H. apply H2. assumption. }
            }
            { right. intros H. inversion H. apply H1. assumption. }
Qed.

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




