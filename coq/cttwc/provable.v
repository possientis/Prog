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
