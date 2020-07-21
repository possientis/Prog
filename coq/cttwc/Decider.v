(* f is a decider for p                                                         *)
Definition Decider (a:Type) (f:a -> bool) (p:a -> Prop) : Prop :=
    forall (x:a), p x <-> f x = true.

Arguments Decider {a}.

Definition Decidable (a:Type) (p:a -> Prop) : Prop :=
    exists (f:a -> bool), Decider f p.

Arguments Decidable {a}.


Definition Decider_ (b:bool) (X:Prop) : Prop :=
    X <-> b = true.

Definition Decidable_ (X:Prop) : Prop :=
    exists (b:bool), Decider_ b X.

Lemma L1 : forall (a:Type) (p:a -> Prop) (f:a -> bool),
    Decider f p <-> forall (x:a), Decider_ (f x) (p x).
Proof.
    unfold Decider, Decider_. intros a p f. split; auto.
Qed.

Lemma L2 : forall (a:Type) (p:a -> Prop), 
    Decidable p -> forall (x:a), Decidable_ (p x).
Proof.
    unfold Decidable, Decidable_, Decider, Decider_. 
    intros a p [f H1] x. exists (f x). apply H1.
Qed.

Lemma L3 : forall (X:Prop),
    Decidable_ X <-> exists (q:{X} + {~X}), True.
Proof.
    unfold Decidable_, Decider_. intros X. split.
    - intros [b H1]. destruct H1 as [H1 H2]. destruct b.
        + assert X as H3. { apply H2. reflexivity. } exists (left H3). trivial.
        + assert (~X) as H3. { intros H3. apply H1 in H3. inversion H3. }
          exists (right H3). trivial.
    - intros [q _]. destruct q as [H1|H1].
        + exists true. split; intros H2.
            { reflexivity. }
            { assumption. }
        + exists false. split; intros H2.
            { exfalso. apply H1. assumption. }
            { inversion H2. }
Qed.

Lemma L4 : forall (a:Type) (p:a -> Prop),
    Decidable p <-> exists (q:forall (x:a), {p x} + {~p x}), True.
Proof.

Show.

(*
Lemma L3 : forall (a:Type) (p:a -> Prop),
    (forall (x:a), Decidable_ (p x)) -> Decidable p.
Proof.

Show.
*)



