Require Import List.

Require Import In.


Lemma concat_charac : forall (v:Type) (xss:list (list v)) (x:v),
    x :: concat xss <-> exists (xs:list v), (x :: xs) /\ (xs :: xss).
Proof.
    intros v. induction xss as [|xs xss IH]; intros x; split; simpl.
    - intros H. contradiction.
    - intros [xs [H1 H2]]. contradiction.
    - intros H. apply in_app_or in H. destruct H as [H|H].
        + exists xs. split.
            { assumption. }
            { left. reflexivity. }
        + destruct (IH x) as [H1 H2]. apply H1 in H. 
          destruct H as [ys [H3 H4]]. exists ys. split.
            { assumption. }
            { right. assumption. }
    - intros [ys [H1 [H2|H2]]].
        + subst. apply in_or_app. left. assumption.
        + apply in_or_app. right. apply IH. exists ys. split; assumption.
Qed.
