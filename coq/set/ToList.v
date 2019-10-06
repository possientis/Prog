Require Import List.
Require Import Arith.Le.

Require Import set.
Require Import nat.
Require Import Order.

Fixpoint toList (x:set) : list set :=
    match x with
    | Nil           => nil
    | (Cons x xs)   => cons x (toList xs)
    end.


Lemma toList_order : forall (x y:set),
    In x (toList y) -> order x <= order y.
Proof.
    intros x. induction y as [|y _ ys IH]; intros H.
    - inversion H.
    - destruct H as [H|H].
        + rewrite <- H. simpl. apply le_S. apply n_le_max.
        + simpl. apply le_S. apply le_trans with (order ys).
            { apply IH. assumption. }
            { apply m_le_max. }
Qed.




