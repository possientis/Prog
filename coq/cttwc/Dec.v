Definition Dec (X:Prop) : Type := {X} + {~X}.

Definition L1 : forall (X Y:Prop), Dec X -> Dec Y -> Dec (X -> Y).
Proof.
    unfold Dec. intros X Y [H1|H1] [H2|H2].
    - left. intros _. assumption.
    - right. intros H3. apply H2, H3. assumption.
    - left. intros H3. apply H1 in H3. contradiction.
    - left. intros H3. apply H1 in H3. contradiction.
Defined.


Definition L2 : forall (X Y:Prop), Dec X -> Dec Y -> Dec (X /\ Y).
Proof.
    unfold Dec. intros X Y [H1|H1] [H2|H2].
    - left. split; assumption.
    - right. intros [H3 H4]. apply H2 in H4. contradiction.
    - right. intros [H3 H4]. apply H1 in H3. contradiction.
    - right. intros [H3 H4]. apply H1 in H3. contradiction.
Defined.


Definition L3 : forall (X Y:Prop), Dec X -> Dec Y -> Dec (X \/ Y).
Proof.
    unfold Dec. intros X Y [H1|H1] [H2|H2].
    - left. left. assumption.
    - left. left. assumption.
    - left. right. assumption.
    - right. intros [H3|H3].
        + apply H1. assumption.
        + apply H2. assumption.
Defined.


Definition L4 : forall (X:Prop), Dec X -> Dec (~X).
Proof.
    unfold Dec. intros X [H1|H1].
    - right. intros H2. apply H2. assumption.
    - left. assumption.
Defined.

Definition L5 : Dec True := left I.

Definition L6 : Dec False := right (fun x => x).

