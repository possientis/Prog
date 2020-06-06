Inductive Provable : Prop -> Prop :=
| PA : forall (X Y:Prop), Provable (X -> Y) -> Provable X -> Provable Y
| PI : forall (X : Prop), Provable (X -> X)
| PK : forall (X Y:Prop), Provable Y -> Provable (X -> Y)
| PN : forall (X Y:Prop), Provable (X -> Y) -> Provable (~Y -> ~X)
.

Definition Contradictory (X:Prop) : Prop := Provable (~X).
Definition Consistent (X:Prop) : Prop := ~Contradictory X.
Definition Independent (X:Prop) : Prop := ~Provable X /\ Consistent X.

Lemma L1 : forall (X Y:Prop), Provable (X -> Y) -> ~Provable Y -> ~Provable X.
Proof.
    intros X Y H1 H2 H3. apply H2. apply PA with X; assumption.
Qed.

Lemma L2 : forall (X Y:Prop), Provable (X -> Y) -> Consistent X -> Consistent Y.
Proof.
    unfold Consistent, Contradictory. intros X Y H1 H2 H3. apply H2.
    apply PA with (~Y).
    - apply PN. assumption.
    - assumption. 
Qed.

Lemma L3 : forall (X Y:Prop), Provable (X -> Y) -> Provable (Y -> X) ->
    Provable X -> Provable Y.
Proof.
    intros X Y H1 H2 H3. apply PA with X; assumption.
Qed.

Lemma L4 : forall (X Y:Prop), Provable (X -> Y) -> Provable (Y -> X) ->
    ~Provable X -> ~Provable Y.
Proof.
    intros X Y H1 H2 H3 H4. apply H3. apply L3 with Y; assumption.
Qed.

Lemma L5 : forall (X Y:Prop), Provable (X -> Y) -> Provable (Y -> X) ->
    Contradictory X -> Contradictory Y.
Proof.
    unfold Contradictory. intros X Y H1 H2 H3. apply PA with (~X).
    - apply PN. assumption.
    - assumption.
Qed.

Lemma L6 : forall (X Y:Prop), Provable (X -> Y) -> Provable (Y -> X) ->
    Consistent X -> Consistent Y.
Proof.
    unfold Consistent. intros X Y H1 H2 H3 H4. apply H3. 
    apply L5 with Y; assumption.
Qed.

Lemma L7 : forall (X Y:Prop), Provable (X -> Y) -> Provable (Y -> X) ->
    Independent X -> Independent Y.
Proof.
    unfold Independent. intros X Y H1 H2 [H3 H4]. split.
    - intros H5. apply H3. apply L3 with Y; assumption.
    - apply L6 with X; assumption.
Qed.


Lemma Sandwich : forall (Y:Prop),
    (exists (X Z:Prop), Provable (X -> Y) /\ Provable (Y -> Z) /\
        Consistent X /\ ~Provable Z) ->
    Independent Y.
Proof.
    intros Y [X [Z [H1 [H2 [H3 H4]]]]]. unfold Independent. split.
    - intros H5. apply H4. apply PA with Y; assumption.
    - unfold Consistent, Contradictory. intros H5.
      unfold Consistent in H3. unfold Contradictory in H3. apply H3.
      apply PA with (~Y).
        + apply PN. assumption.
        + assumption.
Qed.


Definition L8 : Prop := ~Provable False.
Definition L9 : Prop := Consistent (~False).
Definition L10: Prop :=  exists (X:Prop), Consistent X.
Definition L11: Prop := forall (X:Prop), Provable X -> Consistent X.

Lemma L12 : L8 -> L9.
Proof.
    unfold L8, L9, Consistent, Contradictory. intros H1 H2.
    apply H1. apply PA with (False -> False). 
    - assumption.
    - apply PI.
Qed.

Lemma L13 : L9 -> L10.
Proof.
    unfold L9, L10. intros H. exists (~False). assumption.
Qed.

Lemma L14 : L10 -> L8.
Proof.
    unfold L8, L10. intros [X H1]. unfold Consistent, Contradictory in H1.
    intros H2. apply H1. apply PK. assumption.
Qed.

Lemma L15 : L8 -> L11.
Proof.
    unfold L8, L11. intros H1 X H2. unfold Consistent, Contradictory.
    intros H3. apply H1, PA with X; assumption.
Qed.

Lemma L16 : L11 -> L8.
Proof.
    unfold L8, L11. intros H1 H2. apply (H1 False) in H2.
    unfold Consistent, Contradictory in H2. apply H2, PI.
Qed.

Definition PAPred (p:Prop -> Prop) : Prop := 
    forall (X Y:Prop), p (X -> Y) -> p X -> p Y.

Definition PIPred (p:Prop -> Prop) : Prop :=
    forall (X:Prop), p (X -> X).

Definition PKPred (p:Prop -> Prop) : Prop :=
    forall (X Y:Prop), p Y -> p (X -> Y).

Definition PNPred (p:Prop -> Prop) : Prop :=
    forall (X Y:Prop), p (X -> Y) -> p (~ Y -> ~ X).

Definition ProvPred (p:Prop -> Prop) : Prop :=
    PAPred p /\ PIPred p /\ PKPred p /\ PNPred p.

