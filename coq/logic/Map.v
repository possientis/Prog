Require Import List.


Lemma mapIn : forall (v w:Type) (f:v -> w) (y:w) (xs:list v),
    In y (map f xs) -> exists (x:v), In x xs /\ y = f x.
Proof.
    intros v w f y. 
    induction xs as [|x xs IH]; simpl.
    - intros H. exfalso. assumption.
    - intros [H|H]. 
        + exists x. split.
            { left. reflexivity. }
            { symmetry. assumption. }
        + apply IH in H. destruct H as [x' [H1 H2]]. 
          exists x'. split.
            { right. assumption. }
            { assumption. }
Qed.
