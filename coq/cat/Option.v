
Lemma Some_iff_not_None : forall (a:Type) (x:option a),
    x <> None <-> exists y, x = Some y.
Proof.
    intros a x. destruct x as [y|] eqn:H.
    - split.
        + intros _. exists y. reflexivity.
        + intros _ H'. inversion H'.
    - split.
        + intros H'. exfalso. apply H'. reflexivity.
        + intros [y H']. inversion H'.
Qed.


Definition toSomeProof (a:Type) (x:option a) (p:x <> None) : exists y, x = Some y.
Proof. apply Some_iff_not_None in p. exact p. Qed.


Definition fromOption' (a:Type) (x:option a) (p:x <> None) : { y:a | Some y = x }.
Proof.
    destruct x as [y|] eqn: H.
    - exists y. reflexivity.
    - exfalso. apply p. reflexivity.
Qed.


Definition fromOption (a:Type) (x:option a) (p:x <> None) : a :=
   proj1_sig (fromOption' a x p). 


Arguments fromOption {a} _ _.

Lemma fromOption_correct : forall (a:Type) (x:option a) (p:x <> None),
    x = Some (fromOption x p).
Proof.
    intros a x p. unfold fromOption. remember (fromOption' a x p) as z eqn:H.
    clear H. destruct z as [y H']. simpl. rewrite H'. reflexivity. 
Qed.

    




