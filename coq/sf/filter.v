Require Import bool.
Require Import list.
Require Import In.

Fixpoint filter (a:Type) (test: a -> bool) (l:list a) : list a :=
    match l with
    | []        => []
    | x::xs     => if test x then x::filter a test xs else filter a test xs
    end.

Arguments filter {a} _ _.

Lemma filter_of_false : forall (a:Type) (test:a -> bool) (l:list a),
    (forall x, In x l -> test x = false) -> filter test l = [].
Proof.
    intros a test l H. revert H. induction l as [|x xs IH].
    - intros _. reflexivity.
    - intros H. assert (test x = false) as Hx. { apply H. left. reflexivity. }
        simpl. rewrite Hx. apply IH. intros y H'. apply H. right. exact H'.
Qed.

Lemma filter_of_true : forall (a:Type) (test:a -> bool) (l:list a),
    (forall x, In x l -> test x = true) -> filter test l = l.
Proof.
    intros a test l H. revert H. induction l as [|x xs IH].
    - intros _. reflexivity.
    - intros H. assert (test x = true) as Hx. { apply H. left. reflexivity. }
        simpl. rewrite Hx. assert (filter test xs = xs) as H0. 
            { apply IH. intros y H'. apply H. right. exact H'. }
        rewrite H0. reflexivity.
Qed.

Lemma filter_all_true : forall (a:Type) (test:a -> bool) (l:list a),
    forall x, In x (filter test l) -> test x = true.
Proof.
    intros a test l. induction l as [|x xs IH].
    - intros x H. inversion H.
    - intros y H. simpl in H. destruct (test x) eqn:Hx.
        + destruct H as [H|H].
            { rewrite <- H. exact Hx. }
            { apply IH. exact H. }
        + apply IH. exact H.
Qed.





