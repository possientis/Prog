Require Import list.
Require Import fmap.
Require Import nat.
Require Import bool.
Require Import induction.

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


Definition combine_odd_even (Po Pe:nat -> Prop) (n:nat) : Prop :=
    if oddb n then Po n else Pe n.


Theorem combine_odd_even_intro : forall (Po Pe:nat -> Prop) (n:nat),
    (oddb n = true -> Po n)  -> 
    (oddb n = false -> Pe n) -> 
    combine_odd_even Po Pe n.
Proof.
    intros Po Pe n Ho He. destruct (oddb n) eqn:H.
    - unfold combine_odd_even. rewrite H. apply Ho. reflexivity.
    - unfold combine_odd_even. rewrite H. apply He. reflexivity.
Qed.

Theorem combine_odd_even_elim_odd : forall (Po Pe:nat -> Prop) (n:nat),
    combine_odd_even Po Pe n -> oddb n = true -> Po n.
Proof.
    intros Po Pe n H H'. unfold combine_odd_even in H. rewrite H' in H. exact H.
Qed.

Theorem combine_odd_even_elim_even : forall (Po Pe:nat -> Prop) (n:nat),
    combine_odd_even Po Pe n -> oddb n = false -> Pe n.
Proof.
    intros Po Pe n H H'. unfold combine_odd_even in H. rewrite H' in H. exact H.
Qed.


Example lemma_application_ex1 : forall (n:nat) (ns:list nat),
    In n (map (fun m => m * 0) ns) -> n = 0.
Proof.
    intros n ns. induction ns as [|x xs H].
    - intros H. inversion H.
    - simpl. intros [H'|H'].
        + rewrite mult_n_0 in H'. symmetry. exact H'.
        + apply H. exact H'. 
Qed.

