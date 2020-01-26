Ltac basic :=
    match goal with
    |           |- True => trivial
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


Ltac simplify :=
    repeat (intros;
        match goal with
        | H : ~ _               |- _    => red in H
        | H : _ /\ _            |- _    => elim H; do 2 intro; clear H
        | H : _ \/ _            |- _    => elim H; intro; clear H
        | H : ?A /\ ?B -> ?C    |- _    => 
            cut (A -> B -> C); 
                [ intro; clear H 
                | intros; apply H; split; assumption]
        | H : ?A \/ ?B -> ?C    |- _    => 
            cut (B -> C); 
                [ intro; cut (A -> C);
                    [ intro; clear H
                    | intro; apply H; left; assumption ] 
                | intro; apply H; right; assumption]
        end).

Lemma L5 : forall (A:Prop), ~A -> True.
Proof. simplify. trivial. Qed.

Lemma L6 : forall (A B:Prop), A /\ B -> True.
Proof. simplify. trivial. Qed.

Lemma L7 : forall (A B:Prop), A \/ B -> True.
Proof. simplify; trivial. Qed.

Lemma L8 : forall (A B C:Prop), (A /\ B -> C) -> True.
Proof. simplify. trivial. Qed.

Lemma L9 : forall (A B C:Prop), (A \/ B -> C) -> True.
Proof. intros. cut (B -> C); 
            [ intro; cut (A -> C);
                [ intro; clear H
                | intro; apply H; left; assumption ] 
            | intro; apply H; right; assumption].
        trivial.
Qed.

Lemma L9' : forall (A B C:Prop), (A \/ B -> C) -> True.
Proof. intros. simplify. trivial. Qed.


