Require Import Le.
Require Import List.
Require Import Compare_dec.
Import Nat.

Require Import Logic.List.In.

Lemma natMinimal : forall (ns:list nat), ns <> nil ->
    exists (n:nat), n :: ns /\ forall (m:nat), m :: ns -> n <= m.
Proof.
    induction ns as [|x xs IH].
    - intros H. exfalso. apply H. reflexivity.
    - intros _. destruct xs as [|y ys].
        + exists x. split.
            { left. reflexivity. }
            { intros m [H|H].
                { rewrite H. reflexivity. }
                { inversion H. }}
        + assert (cons y ys <> nil) as P. { intros H. inversion H. }
          destruct (IH P) as [n' [H1 H2]].
          destruct (le_le_S_dec x n') as [H3|H3].
            { exists x. split.
                { left. reflexivity. }
                { intros m [H4|[H4|H4]].
                    { rewrite <- H4. apply le_n. }
                    { rewrite <- H4. apply le_trans with n'.
                        { assumption. }
                        { apply H2. left. reflexivity. }}
                    { apply le_trans with n'.
                        { assumption. }
                        { apply H2. right. assumption. }}}}
            { exists n'. split.
                { right. assumption. }
                { intros m [H4|[H4|H4]].
                    { rewrite <- H4. apply le_trans with (S n').
                        { apply le_S, le_n. }
                        { assumption. }}
                    { apply H2. left. assumption. }
                    { apply H2. right. assumption. }}}
Qed.
