Require Import Max.

Require Import Core.Set.

Fixpoint order (xs:set) : nat :=
    match xs with
    | Nil       =>  0
    | Cons x xs =>  1 + max (order x) (order xs)
    end.

Lemma order_0 : forall (xs:set), order xs = 0 -> xs = Nil.
Proof.
    intros [|x xs].
    - intros _. reflexivity.
    - intros H. inversion H.
Qed.


