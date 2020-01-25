Ltac basic :=
    match goal with
    | |- True           => trivial
    | _ : False |- _    => contradiction
    | _ : ?A    |- ?A   => assumption
    end.


Lemma L1 : forall (A:Prop), A -> A.
Proof. intros A p. basic. Qed.


Lemma L2 : True.
Proof. basic. Qed.

Lemma L3 : forall (A:Prop), False -> A.
Proof. intros A H. basic. Qed.

Lemma L4 : forall (A:Prop), ~A -> True.
Proof. intros A H. red in H. trivial. Qed.

