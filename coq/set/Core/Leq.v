Require Import Core.Set.
Require Import Core.Decidability.

(* Ordering of syntactic representations of sets.                               *)
Fixpoint leq (x y:set) : Prop :=
    match x with
    | Nil           => True
    | (Cons x xs)   =>
        match y with
        | Nil           => False
        | (Cons y ys)   => (x <> y) /\ (leq x y)    (* lexicographic order      *)
                        \/ (x = y)  /\ (leq xs ys)
        end
    end.

(* Strict equality between sets is decidable so leq itself is decidable.        *)
Lemma leq_dec : forall (x y:set), {leq x y} + {~leq x y}.
Proof.
    induction x as [|x IH1 xs IH2]; intros y.
    - left. apply I.
    - destruct y as [|y ys].
        + right. simpl. unfold not. intros. contradiction.
        + destruct (set_eq_dec x y) as [H1|H1].
            { destruct (IH2 ys) as [H2|H2].
                { left. right. split; assumption. }
                { right. simpl. intros [[H3 H4]|[H3 H4]].
                    { apply H3 in H1. contradiction. }
                    { apply H2 in H4. contradiction. }}}
            { destruct (IH1 y) as [H2|H2].
                { left. left. split; assumption. }
                { right. simpl. intros [[H3 H4]|[H3 H4]].
                    { apply H2 in H4. contradiction. }
                    { apply H1 in H3. contradiction. }}}
Qed.

Lemma leq_refl : forall (x:set), leq x x.
Proof.
    induction x as [|x _ xs IH].
    - apply I.
    - right. split.
        + reflexivity.
        + apply IH.
Qed.
