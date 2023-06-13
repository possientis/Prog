(* NEXT: ===> Core                                                              *) 

Require Import Le.
Require Import List.
Import Nat.

Require Import Logic.Nat.Max.

Require Import Logic.Set.Set.


(* Now that we have a type to represent our universe of sets, we shall need     *)
(* to define various notions in relation to it. For example we shall need to    *) 
(* define what it means for a set x to belong to a set y (denoted x :: y), or   *)
(* what it means for a set x to be a subset of y (denoted x <== y), or what it  *)
(* means for a set x to be equal to y (denoted x == y). These relations can be  *)
(* defined in coq in any way we like. However, if we want our model of set      *)
(* theory to be interesting, we shall need to use definitions which are more    *)
(* complex than simple recursive definitions. In particular, we shall need to   *)
(* reason on the 'complexity' of the arguments, as measured by the 'order'.     *)
Fixpoint order (xs:set) : nat :=
    match xs with
    | Nil       =>  0
    | Cons x xs =>  S (max (order x) (order xs))
    end.

(* This lemma will be used on many occasions. If a set x is one of the elements *)
(* of the list of sets associated with a set y, then the 'complexity' of x      *)
(* cannot be greater to that of y. In fact a stronger result with a strict      *)
(* inequality can be obtained, but this has not been needed so far.             *)
Lemma orderToList : forall (x y:set),
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

(* The only set with order 0 is Nil.                                            *)
Lemma order_0 : forall (xs:set), order xs = 0 -> xs = Nil.
Proof.
    intros [|x xs].
    - intros _. reflexivity.
    - intros H. inversion H.
Qed.
