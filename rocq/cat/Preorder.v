Record Preorder (A:Type) : Type := preorder
    {   rel : A -> A -> Prop
    ;   proof_refl : forall x:A, rel x x
    ;   proof_trans: forall x y z:A, rel x y -> rel y z -> rel x z
    }
    .


Arguments preorder {A} _ _ _.
Arguments rel {A} _ _ _.
Arguments proof_refl {A} _ _.
Arguments proof_trans {A} _ _ _ _ _ _.

Lemma eq_rel : forall (A:Type) (p:Preorder A), forall (x x' y y':A),
    x = x' -> y = y' -> rel p x y = rel p x' y'.
Proof.
    intros A p x x' y y' Exx Eyy. rewrite Exx, Eyy. reflexivity.
Qed.


