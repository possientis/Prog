Parameter A : Type.

Axiom Lem_Eq : forall x y:A, {x = y} + {x <> y}.

Definition eqb (x y: A) : bool.
Proof.
    assert ({x=y}+{x<>y}) as H. {apply Lem_Eq. }
    destruct H as [H|H]. 
    - exact true.
    - exact false.
Qed.

Check eqb.

Definition eqb' (x y: A) : bool :=
    if eqb x y then true else false.
