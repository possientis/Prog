Ltac find_if :=
    match goal with
    | [ |- if ?X then _ else _ ] => destruct X
    end.

Lemma L1 : forall (a b c:bool),
    if a 
        then if b
            then True
            else True
        else if c
            then True
            else True.
Proof.
    intros. find_if; find_if; constructor.
Qed. 


Ltac find_if_inside :=
    match goal with
    | [ |- context[if ?X then _ else _] ] => destruct X
    end.

(* find_if cannot crack this *)
Lemma L2 : forall (a b:bool),
    (if a then 42 else 42) = (if b then 42 else 42).
Proof.
    intros. find_if_inside; find_if_inside; reflexivity.
Qed.
