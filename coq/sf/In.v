Require Import list.
Require Import fmap.

Fixpoint In (a:Type) (x:a) (l:list a) : Prop :=
    match l with
    | []        => False
    | y :: xs   => y = x \/ In a x xs
    end.

Arguments In {a} _ _.


Example test_In1 : In 4 [3,4,5].
Proof. simpl. right. left. reflexivity. Qed.


Example test_In2 : forall n, 
    In n [2,4] -> exists m, n = 2 * m.
Proof.
    simpl. intros n [H|[H|H]].
    - exists 1. symmetry in H. apply H.
    - exists 2. symmetry in H. apply H.
    - inversion H.
Qed.


Lemma In_map : forall (a b:Type) (f:a -> b) (l:list a) (x:a),
    In x l -> In (f x) (map f l).
Proof.
    intros a b f l x. induction l as [|y ys H].
    - intros H. inversion H.
    - simpl. intros [H'|H'].
        + left. rewrite H'. reflexivity.
        + right. apply H. apply H'.
Qed.


