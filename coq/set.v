Inductive set : Type :=
| mkset : forall (a:Type) (f:a -> set), set
.


Definition setEq (x y:set) : Prop :=
    match x with 
    | mkset a f     =>
        match y with
        | mkset b g     =>
            (forall (z:a), exists (z':b), f z = g z') /\
            (forall (z:b), exists (z':a), g z = f z')
        end
    end.

Lemma reflSet : forall (x:set), setEq x x.
Proof.
    intros [a f]. unfold setEq. split;
    intros z; exists z; reflexivity.
Qed.

Lemma symSet : forall (x y:set), setEq x y -> setEq y x.
Proof.
    intros [a f] [b g]. unfold setEq. intros [H1 H2]. split; assumption.
Qed.

Lemma transSet : forall (x y z:set), setEq x y -> setEq y z -> setEq x z.
Proof.
    intros [a f] [b g] [c h]. unfold setEq. intros [H1 H2] [H3 H4]. split.
    - intros z. destruct (H1 z) as [z' K]. destruct (H3 z') as [z'' L].
      exists z''. rewrite K. assumption.
    - intros z. destruct (H4 z) as [z' K]. destruct (H2 z') as [z'' L].
      exists z''. rewrite K. assumption.
Qed.
