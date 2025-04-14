Require Import Le.
Require Import Nat.
Require Import Compare_dec.
Import Nat.

Fixpoint blt_nat (n m:nat) : bool :=
    match n with
    | 0 => 
        match m with
        | 0     => false
        | S _   => true
        end
    | S n'  =>
        match m with
        | 0     => false
        | S m'  => blt_nat n' m'
        end
    end.

Lemma nat_dec : forall (n m:nat), {n = m} + {n <> m}.
Proof.
    induction n as [|n IH].
    - destruct m as [|m].
        + left. reflexivity.
        + right. intros H. inversion H.
    - destruct m as [|m].
        + right. intros H. inversion H.
        + destruct (IH m) as [H|H].
            { left. rewrite H. reflexivity. }
            { right. intros H'. apply H. inversion H'. reflexivity. }
Qed.

Lemma plus_n_n : forall (n:nat), n + n = 2*n.
Proof.
    destruct n as [|n].
    - reflexivity.
    - simpl. rewrite <- plus_n_Sm, <- plus_n_Sm, <- plus_n_O. reflexivity.
Qed.


Lemma max_lub : forall (n m p:nat), n <= p -> m <= p -> max n m <= p.
Proof.
    intros n m p H1 H2. destruct (le_dec n m) as [H|H].
    - rewrite max_r; assumption.
    - rewrite max_l.
        + assumption.
        + apply not_le in H. unfold gt in H. unfold lt in H.
          apply le_trans with (S m). 
            { apply le_S, le_n. }
            { assumption. }
Qed.
