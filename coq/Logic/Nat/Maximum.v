Require Import Le.
Require Import List.

Require Import Logic.Nat.Max.

Fixpoint maximum (ns:list nat) : nat :=
    match ns with
    | nil       => 0
    | cons n ns => max n (maximum ns)
    end.    

Lemma maximum_lub : forall (ns:list nat) (N:nat), 
    (forall (n:nat), In n ns -> n <= N) -> maximum ns <= N.
Proof.
    intros ns N. induction ns as [|n ns IH].
    - intros _. apply le_0_n.
    - intros H. simpl. apply max_lub.
        + apply H. left. reflexivity.
        + apply IH. intros m Hm. apply H. right. assumption.
Qed.

Lemma maximum_ubound : forall (ns:list nat) (n:nat),
    In n ns -> n <= maximum ns.
Proof.
    induction ns as [|n' ns IH].
    - intros n H. inversion H.
    - intros n [H|H].
        + subst. apply n_le_max.
        + apply le_trans with (maximum ns).
            { apply IH. assumption. }
            { apply m_le_max. }
Qed.


