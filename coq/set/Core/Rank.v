Require Import Le.
Require Import List.

Require Import Core.Nat.
Require Import Core.Set.
Require Import Core.Equal.
Require Import Core.Decidability.

Fixpoint rank (xs:set) : nat :=
    match xs with 
    | Nil       => 0
    | Cons x xs => 
       match rank xs with
        | 0     => S (rank x)
        | S r   => S (max (rank x) r)
        end 
    end.
(* The rank is 0 if and only if the set is empty                                *)
Lemma rank_Nil : forall (x:set), rank x = 0 <-> x = Nil.
Proof.
    intros x. destruct x as [|x xs]; split.
    - intros. reflexivity.
    - intros. reflexivity.
    - simpl. destruct (rank xs) as [|n]; intros H; inversion H.
    - intros H. inversion H.
Qed.

(* When not empty, the rank is 1 + the maximum of the ranks of the elements     *)
Lemma rank_maximum : forall (x:set), x <> Nil -> 
    rank x = S (maximum (map rank (toList x))).
Proof.
    induction x as [|x IH1 xs IH2].
    - intros H. exfalso. apply H. reflexivity.
    - simpl. intros _. destruct (rank xs) as [|n] eqn:E.
        + apply rank_Nil in E. rewrite E. simpl. rewrite max_n_0. reflexivity.
        + assert (xs <> Nil) as H'.
            { intros H1. rewrite H1 in E. inversion E. }
          apply IH2 in H'. inversion H'. reflexivity.
Qed.


Lemma rank_compat : forall (x y:set), x == y -> rank x = rank y.
Proof.
    intros x y. remember (rank x) as n eqn:E. 
    assert (rank x <= n) as H. { rewrite E. apply le_n. }
    rewrite E. clear E. revert n x y H. induction n as [|n IH].
    - admit. 
    - intros x y H E. apply le_antisym.
        + destruct (equal_dec x Nil) as [H1|H1].
            { admit. }
            { rewrite rank_maximum with x.
                { rewrite rank_maximum with y.
                    { apply le_n_S.

Show.



