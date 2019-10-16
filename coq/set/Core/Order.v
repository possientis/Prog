Require Import Le.
Require Import Max.
Require Import List.

Require Import Core.Set.
Require Import Core.Nat.

Fixpoint order (xs:set) : nat :=
    match xs with
    | Nil       =>  0
    | Cons x xs =>  S (max (order x) (order xs))
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

Lemma order_0 : forall (xs:set), order xs = 0 -> xs = Nil.
Proof.
    intros [|x xs].
    - intros _. reflexivity.
    - intros H. inversion H.
Qed.


