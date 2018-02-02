Require Import list.
Require Import fmap.

Fixpoint In (a:Type) (x:a) (l:list a) : Prop :=
    match l with
    | []        => False
    | y :: xs   => y = x \/ In a x xs
    end.

Arguments In {a} _ _.



Lemma In_map : forall (a b:Type) (f:a -> b) (l:list a) (x:a),
    In x l -> In (f x) (map f l).
Proof.
    intros a b f l x. induction l as [|y ys H].
    - intros H. inversion H.
    - simpl. intros [H'|H'].
        + left. rewrite H'. reflexivity.
        + right. apply H. apply H'.
Qed.

Lemma In_map_iff : forall (a b:Type) (f:a -> b) (l:list a) (y:b),
    In y (map f l) <-> exists x, f x = y /\ In x l.
Proof.
    intros a b f l y. split.
    - induction l as [|x xs H].
        + intros H. inversion H.
        + simpl. intros [H'|H'].
            { exists x. split. 
                { exact H'. }
                { left. reflexivity. }}
            { apply H in H'. destruct H' as [x' H']. destruct H' as [H1 H2].  
                exists x'. split.
                    { exact H1. }
                    { right. exact H2. }}
    - intros [x [H1 H2]]. rewrite <- H1. apply In_map. exact H2.
Qed.


Lemma In_app_iff : forall (a:Type) (l k:list a) (x:a),
    In x (l ++ k) <-> In x l \/ In x k.
Proof.
    intros a l k x. split.
    - induction l as [|y xs H].
        + simpl. intros H. right. exact H.
        + simpl. intros [H'|H'].
            { left. left. exact H'. }
            { apply H in H'. destruct H' as [H1|H2].
                { left. right. exact H1. }
                { right. exact H2. }}
    - induction l as [|y xs H]. 
        + intros [H'|H'].
            { inversion H'. }
            { exact H'. }
        + simpl. intros [[H'|H']|H'].
            { left. exact H'. }
            { right. apply H. left. exact H'. }
            { right. apply H. right. exact H'. }
Qed.


Fixpoint All (a:Type) (P:a -> Prop) (l:list a) : Prop :=
    match l with
    | []        => True
    | x :: xs   => P x /\ All a P xs
    end.

Arguments All {a} _ _.

Lemma All_In : forall (a:Type) (P:a -> Prop) (l:list a),
    (forall x, In x l -> P x) <-> All P l.
Proof.
    intros a P l. split.
    - induction l as [|x xs H].
        + intros. reflexivity.
        + simpl. intros H'. split.
            { apply H'. left. reflexivity. }
            { apply H. intros x' H0. apply H'. right. exact H0. }
    - induction l as [|x xs H].
        + intros H x H'. inversion H'.
        + simpl. intros [H1 H2] x'[H'|H'].
            { rewrite <- H'. exact H1. }
            { apply H. exact H2. exact H'. }
Qed.

Lemma In_split : forall (a:Type)(x:a)(l:list a), 
    In x l -> exists k m, l = k ++ x :: m.
Proof.
    intros a x l. induction l as [|y xs IH].
    - intros H. inversion H.
    - intros [H|H].
        + exists [], xs. simpl. rewrite H. reflexivity.
        + apply IH in H. clear IH. destruct H as [k [m H]].
            exists (y :: k), m. rewrite H. rewrite app_cons. reflexivity.
Qed.



