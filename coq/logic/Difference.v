Require Import List.
Import ListNotations.

Require Import Eq.

Fixpoint diff (v:Type) (e:Eq v) (xs ys:list v) : list v :=
    match xs with
    | []        => []
    | (x :: xs) =>
        match in_dec eqDec x ys with
        | left  _   => diff v e xs ys
        | right _   => x :: diff v e xs ys
        end
    end.
Arguments diff {v} {e}.

Notation "xs \\ ys" := (diff xs ys) 
    (at level 50, left associativity) : Difference_scope.

Open Scope Difference_scope.

Lemma diff_charac : forall (v:Type) (e:Eq v) (xs ys:list v) (z:v),
    In z (xs \\ ys) <-> In z xs /\ ~In z ys.
Proof.
    intros v e xs ys z. split.
    - induction xs as [|x xs IH]; intros H.
        + inversion H.
        + destruct (in_dec eqDec x ys) as [H'|H'] eqn:E; 
          simpl in H; rewrite E in H.
            { apply IH in H. destruct H as [H1 H2]. split.
                { right. assumption. }
                { assumption. }
            }
            { destruct H as [H|H].
                { subst. split.
                    { left. reflexivity. }
                    { assumption. }
                }
                { apply IH in H. destruct H as [H1 H2]. split.
                    { right. assumption. }
                    { assumption. }
                }
            }
    - induction xs as [|x xs IH]; intros [H1 H2].
        + inversion H1.
        + destruct (in_dec eqDec x ys) as [H|H] eqn:E; simpl; rewrite E.
            { destruct H1 as [H1|H1].
                { subst. exfalso. apply H2. assumption. }
                { apply IH. split; assumption. }
            }
            { destruct H1 as [H1|H1].
                { subst. left. reflexivity. }
                { right. apply IH. split; assumption. }
            }
Qed.
