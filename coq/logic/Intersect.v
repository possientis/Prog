Require Import List.
Import ListNotations.

Require Import Eq.

Fixpoint inter (v:Type) (e:Eq v) (xs ys:list v) : list v :=
    match xs with
    | []        => []
    | (x :: xs) => 
        match in_dec eqDec x ys with
        | left  _   => x :: inter v e xs ys
        | right _   => inter v e xs ys
        end
    end.

Arguments inter {v} {e}.

Notation "xs /\ ys" := (inter xs ys)
    (at level 80, right associativity) : Intersect.

Open Scope Intersect.

Lemma inter_charac : forall (v:Type) (e:Eq v) (xs ys:list v) (z:v),
    In z (xs /\ ys) <-> In z xs /\ In z ys.
Proof.
    intros v e xs ys z. split.
    - induction xs as [|x xs IH]; intros H.
        + inversion H.
        + destruct (in_dec eqDec x ys) as [H'|H'] eqn:E; 
          simpl in H; rewrite E in H.
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
            { apply IH in H. destruct H as [H1 H2]. split.
                { right. assumption. }
                { assumption. }
            }
   - induction xs as [|x xs IH]; intros [H1 H2].
        + inversion H1.
        + destruct (in_dec eqDec x ys) as [H|H] eqn:E; simpl; rewrite E.
            { destruct H1 as [H1|H1].
                { subst. left. reflexivity. }
                { right. apply IH. split; assumption. }
            }
            { destruct H1 as [H1|H1]. 
                { subst. exfalso. apply H. assumption. }
                { apply IH. split; assumption. }
            } 
Qed.
