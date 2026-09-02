Require Import List.
Import ListNotations.

Lemma map_invariant : forall (v:Type) (f:v -> v) (l:list v),
    (forall (x:v), In x l -> f x = x) -> map f l = l.
Proof.
    intros v f l. induction l as [|a l IH]; intros H; simpl.
    - reflexivity.
    - rewrite H.
        + rewrite IH. 
            { reflexivity. }
            { intros x Hx. apply H. right. assumption. }
        + left. reflexivity.
Qed.
