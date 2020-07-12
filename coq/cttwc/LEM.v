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

(* Counterexample                                                               *)
Definition LEM6 : Prop := forall (a:Type) (p:a -> Prop), 
    (forall (x:a), p x) \/ exists (x:a), ~p x.

Lemma L161 : LEM1 <-> LEM6.
Proof.
    unfold LEM1, LEM6. split; intros H.
    - intros a p. destruct (H (exists x, ~p x)) as [H1|H1].
        + right. assumption.
        + left. intros x. destruct (H (p x)) as [H2|H2].
            { assumption. }
            { exfalso. apply H1. exists x. assumption. }
    - intros X. destruct (H unit (fun _ => X)) as [H1|H1].
        + left. apply H1. exact tt.
        + destruct H1 as [u H1]. right. assumption.
Qed.


(* De Morgan law for disjunction. Provable without LEM                          *)
Definition MOR1 : Prop := forall (X Y:Prop), ~(X \/ Y) <-> ~X /\ ~Y.

Lemma M1 : MOR1.
Proof.
    unfold MOR1. intros X Y. split; intros H.
    - split; intros H1; apply H.
        + left. assumption.
        + right. assumption.
    - destruct H as [H1 H2]. intros [H3|H3].
        + apply H1 in H3. contradiction.
        + apply H2 in H3. contradiction.
Qed.

(* De Morgan law for existential quantification. Provable without LEM           *)
Definition MOR2 : Prop := forall (a:Type) (p:a -> Prop), 
~(exists (x:a), p x) <-> forall (x:a), ~p x.

Lemma M2 : MOR2.
Proof.
    unfold MOR2. intros a p. split; intros H.
    - intros x H1. apply H. exists x. assumption.
    - intros [x H1]. apply (H x). assumption.
Qed.

(* De Morgan law for conjunction: right to left. Provable without LEM           *)
Definition MOR3RL : Prop := forall (X Y:Prop), ~X \/ ~Y -> ~(X /\ Y).

Lemma M3RL : MOR3RL.
Proof.
    unfold MOR3RL. intros X Y [H|H] [H1 H2]; apply H; assumption.
Qed.


(* De Morgan law for conjunction: left to right. Provable *with* LEM            *)
Definition MOR3LR : Prop := forall (X Y:Prop), ~(X /\ Y) -> ~X \/ ~Y.

Lemma M3LR : LEM1 -> MOR3LR.
Proof.
    unfold LEM1, MOR3LR. intros L X Y H. destruct (L X) as [H1|H1].
    - right. intros H2. apply H. split; assumption.
    - left. assumption.
Qed.

(* De Morgan law for universal quantification: right to left. Provable no LEM   *)
Definition MOR4RL : Prop := forall (a:Type) (p:a -> Prop), 
    (exists (x:a), ~ p x) -> ~ (forall (x:a), p x).

Lemma M4RL : MOR4RL.
Proof.
    unfold MOR4RL. intros a p [x H1] H2. apply H1, H2.
Qed.

(* De Morgan law for universal quantification: left to right. Provable *with*   *)
Definition MOR4LR : Prop := forall (a:Type) (p:a -> Prop), 
    ~ (forall (x:a), p x) -> exists (x:a), ~ p x.

Lemma M4LR : LEM1 -> MOR4LR.
Proof.
    unfold LEM1, MOR4LR. intros L a p H1. 
    destruct (L (exists x, ~p x)) as [H2|H2].
    - assumption.
    - exfalso. apply H1. intros x. destruct (L (p x)) as [H3|H3].
        + assumption.
        + exfalso. apply H2. exists x. assumption.
Qed.

(* Classical implication: right to left. Provable without LEM                   *)
Definition CIRL : Prop := forall (X Y:Prop), ~X \/ Y -> X -> Y.

Lemma ClassRL : CIRL.
Proof.
    unfold CIRL. intros X Y. intros [H1|H1] H2.
    - apply H1 in H2. contradiction.
    - assumption.
Qed.

(* Classical implication: left to right. Provable *with* LEM                   *)
Definition CILR : Prop := forall (X Y:Prop), (X -> Y) -> ~X \/ Y.


Lemma ClassLR : LEM1 -> CILR.
Proof.
    unfold LEM1, CILR. intros L X Y H1. destruct (L Y) as [H2|H2].
    - right. assumption.
    - left. intros H3. apply H2, H1. assumption.
Qed.

(* LEM is needed for left to right.                                             *)
Lemma EX1 : forall (a:Type) (p:a -> Prop), LEM1 -> 
    ~(exists (x:a), ~p x) <-> forall (x:a), p x.
Proof.
    unfold LEM1. intros a p L. split; intros H1.
    - intros x. destruct (L (p x)) as [H2|H2].
        + assumption.
        + exfalso. apply H1. exists x. assumption.
    - intros [x H2]. apply H2, H1.
Qed.

(* LEM is needed for left to right.                                             *)
Lemma EX2 : forall (a:Type) (p:a -> Prop), LEM1 ->
    ~(exists (x:a), ~p x) <-> ~~forall (x:a), p x.
Proof.
    unfold LEM1. intros a p L. split; intros H1.
    - intros H2. apply H2. intros x. destruct (L (p x)) as [H3|H3].
        + assumption.
        + exfalso. apply H1. exists x. assumption.
    - intros [x H2]. apply H1. intros H3. apply H2, H3.
Qed,
