Axiom Type_eq_dec : forall A B:Type, {A = B} + {A <> B}.

Definition Type_eqb (x y:Type):bool. 
Proof.
    assert ( {x = y} + {x <> y} ). { apply Type_eq_dec. }
    destruct H.
        - exact true.
        - exact false.
Qed.

