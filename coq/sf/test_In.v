Require Import bool.
Require Import nat.
Require Import list.
Require Import fmap.
Require Import In.
Require Import induction.

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


