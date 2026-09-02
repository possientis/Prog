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
        | H0 : ?A -> ?B, H1 : ?A |- _   =>
            cut B;
                [ intro; clear H0 
                | apply H0; assumption  
                ]
        end).


Ltac my_auto :=
    simplify; basic ||
    match goal with
    | H : (?A -> ?B) -> ?C |- _     =>
        cut (B -> C);
            [ intro; cut (A -> B);
                [ intro; cut C;
                    [intro; clear H | apply H; assumption ]
                | clear H ]
            | intro; apply H; intro; assumption ]; my_auto
    | H : ~ ?A -> ?B |- _    =>
        cut (False -> B);
            [ intro; cut (A -> False);
                [ intro; cut B;
                    [intro; clear H | apply H; assumption ]
                | clear H ]
            | intro; apply H; red; intro; assumption ]; my_auto
    | |- _ \/ _ => (left; my_auto) || (right; my_auto)
    end.

Lemma L5 : forall (A:Prop), ~A -> True.
Proof. simplify. trivial. Qed.

Lemma L6 : forall (A B:Prop), A /\ B -> True.
Proof. simplify. trivial. Qed.

Lemma L7 : forall (A B:Prop), A \/ B -> True.
Proof. simplify; trivial. Qed.

Lemma L8 : forall (A B C:Prop), (A /\ B -> C) -> True.
Proof. simplify. trivial. Qed.

Lemma L9 : forall (A B C:Prop), (A \/ B -> C) -> True.
Proof. 
    intros. cut (B -> C); 
        [ intro; cut (A -> C);
            [ intro; clear H
            | intro; apply H; left; assumption ] 
        | intro; apply H; right; assumption].
    trivial.
Qed.

Lemma L9' : forall (A B C:Prop), (A \/ B -> C) -> True.
Proof. intros. simplify. trivial. Qed.


Lemma L10 : forall (A B:Prop), (A -> B) -> A -> True.
Proof. 
    intros A B H0 H1. cut B; 
        [ intro; clear H0 
        | apply H0; assumption ].
    trivial.
Qed.

Lemma L10' : forall (A B:Prop), (A -> B) -> A -> True.
Proof. intros. simplify. trivial. Qed.

Lemma L11 : forall (A B C:Prop), ((A -> B) -> C) -> True.
Proof.
    intros A B C H.
    cut (B -> C);
        [ intro; cut (A -> B);
            [ intro; cut C;
                [ intro; clear H
                | apply H; assumption ]
            | clear H] 
        | intro; apply H; intro; assumption].
    - trivial.
    - Abort.

Lemma L12 : forall (A B:Prop), (~A -> B) -> True.
Proof.
    intros A B H.
        cut (False -> B);
            [ intro; cut (A -> False);
                [ intro; cut B;
                    [ intro; clear H
                    | apply H; assumption ]
                | clear H]
            | intro; apply H; red; intro; assumption ].
    - trivial.
    - Abort.


Lemma L13 : forall (A B:Prop), A /\ B -> A \/ B.
Proof. my_auto. Qed.

Lemma L14 : forall (A B:Prop), (~ ~ B -> B) -> (A -> B) -> ~ ~ A -> B.
Proof. my_auto. Qed.
