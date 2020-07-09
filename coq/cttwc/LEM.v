(* Law of excluded middle                                                       *)
Definition LEM1 : Prop := forall (X:Prop), X \/ ~X.

(* Double negation                                                              *)
Definition LEM2 : Prop := forall (X:Prop), ~~X -> X.

(* Contraposition                                                               *)
Definition LEM3 : Prop := forall (X Y:Prop), (~ X ->  ~Y) -> Y -> X.

(* Peirce's law                                                                 *)
Definition LEM4 : Prop := forall (X Y:Prop), ((X -> Y) -> X) -> X.

Definition LEM5 : Prop := forall (X:Prop), (X <-> True) \/ (X <-> False).

Lemma L12 : LEM1 -> LEM2.
Proof.
    unfold LEM1, LEM2. intros L X H1. destruct (L X) as [H2|H2].
    - assumption.
    - apply H1 in H2. contradiction.
Qed.

Lemma L23 : LEM2 -> LEM3.
Proof.
    unfold LEM2, LEM3. intros L X Y H1 H2. apply L. intros H3.
    apply H1 in H3. apply H3 in H2. contradiction.
Qed.

Lemma L34 : LEM3 -> LEM4.
Proof.
    unfold LEM3, LEM4. intros L X Y. apply L. intros H1 H2. apply H1, H2.
    intros H3. exfalso. apply H1. assumption.
Qed.

Lemma L41 : LEM4 -> LEM1.
Proof.
    unfold LEM4, LEM5. intros L X. apply L with False. intros H1.
    right. intros H2. apply H1. left. assumption.
Qed.

Lemma L151: LEM1 <-> LEM5.
Proof.
    unfold LEM1, LEM5. split; intros H1 X.
    - destruct (H1 X) as [H2|H2].
        + left. split; auto.
        + right. split. 
            { assumption. }
            { intros. contradiction. }
    - destruct (H1 X) as [H2|H2].
        + left. apply H2. trivial.
        + right. intros H3. apply H2. assumption.
Qed.





