Definition LEM : Prop := forall (X:Prop), X \/ ~X.

Definition Definite (X:Prop) : Prop := X \/ ~X.
Definition Stable (X:Prop) : Prop := ~~X -> X.

Lemma L1 : forall (X:Prop), Definite X -> Stable X.
Proof.
    unfold Definite, Stable. intros X [H1|H1] H2.
    - assumption.
    - apply H2 in H1. contradiction.
Qed.


Lemma L2 : forall (X:Prop), Stable (~X).
Proof.
    unfold Stable. intros X H1 H2. apply H1. intros H3. apply H3. assumption.
Qed.

Lemma L3 : Definite True /\ Stable True.
Proof.
    unfold Definite, Stable. split.
    - left. trivial.
    - intros H. trivial.
Qed.

Lemma L4 : Definite False /\ Stable False.
Proof.
    unfold Definite, Stable. split.
    - right. auto.
    - intros H. apply H. intros H'. contradiction.
Qed.

Lemma L5 : forall (X Y:Prop), X <-> Y -> Stable X -> Stable Y.
Proof.
    unfold Stable. intros X Y [H1 H2] H3 H4. 
    apply H1, H3. intros H5. apply H4. intros H6. apply H5, H2. assumption.
Qed.

Lemma L6 : forall (X Y:Prop), X <-> Y -> Definite X -> Definite Y.
Proof.
    unfold Definite. intros X Y [H1 H2] [H3|H3].
    - left. apply H1. assumption.
    - right. intros H4. apply H3. apply H2. assumption.
Qed.

Lemma L7 : LEM -> forall (X:Prop), Stable X /\ Definite X.
Proof.
    unfold LEM, Stable, Definite. intros L X. split.
    - intros H. destruct (L X) as [H1|H1].
        + assumption.
        + exfalso. apply H. assumption.
    - apply L.
Qed.

Lemma L8 : forall (X Y:Prop), Definite X -> Definite Y -> Definite (X -> Y).
Proof.
    unfold Definite. intros X Y [H1|H1] [H2|H2].
    - left. intros H3. assumption.
    - right. intros H3. apply H2, H3. assumption.
    - left. intros H3. assumption.
    - left. intros H3. exfalso. apply H1. assumption.
Qed.

Lemma L9 : forall (X Y:Prop), Definite X -> Definite Y -> Definite (X /\ Y).
Proof.
    unfold Definite. intros X Y [H1|H1] [H2|H2].
    - left. split; assumption.
    - right. intros [H3 H4]. apply H2. assumption.
    - right. intros [H3 H4]. apply H1. assumption.
    - right. intros [H3 H4]. apply H1. assumption.
Qed.

Lemma L10 : forall (X Y:Prop), Definite X -> Definite Y -> Definite (X \/ Y).
Proof.
    unfold Definite. intros X Y [H1|H1] [H2|H2].
    - left. left. assumption.
    - left. left. assumption.
    - left. right. assumption.
    - right. intros [H3|H3].
        + apply H1. assumption.
        + apply H2. assumption.
Qed.    

Lemma L11 : forall (X:Prop), Definite X -> Definite (~X).
Proof.
    unfold Definite. intros X [H1|H1].
    - right. intros H2. apply H2. assumption.
    - left. assumption.
Qed.

Lemma L12 : forall (X Y:Prop), 
    Definite X \/ Definite Y -> ~(X /\ Y) <-> ~X \/ ~Y.
Proof.
    unfold Definite. intros X Y [[H1|H1]|[H1|H1]]; split; intros H2.
    - right. intros H3. apply H2. split; assumption.
    - intros [H3 H4]. destruct H2 as [H2|H2]; apply H2; assumption.
    - left. assumption.
    - intros [H3 H4]. destruct H2 as [H2|H2]; apply H2; assumption.
    - left. intros H3. apply H2. split; assumption.
    - intros [H3 H4]. destruct H2 as [H2|H2]; apply H2; assumption.
    - right. assumption.
    - intros [H3 H4]. destruct H2 as [H2|H2]; apply H2; assumption.
Qed.

Lemma L13 : forall (X Y:Prop), Stable Y -> Stable (X -> Y).
Proof.
    unfold Stable. intros X Y H1 H2 H3. apply H1. intros H4. apply H2.
    intros H5. apply H4, H5. assumption.
Qed.

Lemma L14 : forall (X Y:Prop), Stable X -> Stable Y -> Stable (X /\ Y).
Proof.
    unfold Stable. intros X Y H1 H2 H3. split.
    - apply H1. intros H4. apply H3. intros [H5 H6]. apply H4. assumption.
    - apply H2. intros H4. apply H3. intros [H5 H6]. apply H4. assumption.
Qed.

Lemma L15 : forall (a:Type) (p:a -> Prop), 
    (forall (x:a), Stable (p x)) -> Stable (forall (x:a), p x).
Proof.
    unfold Stable. intros a p H1 H2 x. apply H1. intros H3. apply H2.
    intros H4. apply H3, H4.
Qed.

Definition Markov : Prop := forall (f:nat -> bool),
    ~(forall n, f n = false) -> exists n, f n = true.

Lemma L16 : Markov <-> 
    forall (f:nat -> bool), Stable (exists (n:nat), f n = true).
Proof.
    unfold Markov, Stable. split; intros H1 f H2.
    - apply H1. intros H3. apply H2. intros [n H4].
      rewrite (H3 n) in H4. inversion H4.
    - apply H1. intros H3. apply H2. intros n. destruct (f n) eqn:E.
        + exfalso. apply H3. exists n. assumption.
        + reflexivity.
Qed.

Lemma L17 : forall (a:Type) (p:a -> Prop), 
    (forall (x:a), Stable (p x)) -> 
        ~(forall (x:a), p x) <-> ~~exists (x:a), ~p x.
Proof.
    unfold Stable. intros a p H1. split; intros H2 H3.
    - apply H2. intros x. apply H1. intros H4. 
      apply H3. exists x. assumption.
    - apply H2. intros [x H4]. apply H4, H3.
Qed.

(* Classical definition of conjunction.                                         *)
Definition And (X Y:Prop) : Prop := (X -> Y -> False) -> False.

(* Classical definition of disjunction.                                         *)
Definition Or  (X Y:Prop) : Prop := (X -> False) -> (Y -> False) -> False.

(* Classical definition of existence.                                           *)
Definition Exi (a:Type) (p:a -> Prop) : Prop := 
    (forall (x:a), p x -> False) -> False.

Arguments Exi {a}.

(* Classical version implied by original.                                       *)
Lemma L18 : forall (X Y:Prop), X /\ Y -> And X Y.
Proof.
    unfold And. intros X Y [H1 H2] H3. apply H3; assumption.
Qed.

(* Classical version implied by original.                                       *)
Lemma L19 : forall (X Y:Prop), X \/ Y -> Or X Y.
Proof.
    unfold Or. intros X Y [H1|H1] H2 H3.
    - apply H2. assumption.
    - apply H3. assumption.
Qed.

(* Classical version implied by original.                                       *)
Lemma L20 : forall (a:Type) (p:a -> Prop),
    (exists (x:a), p x) -> Exi p.
Proof.
    unfold Exi. intros a p [x H1] H2. apply (H2 x). assumption.
Qed.

(* Classical version is equivalent to double negation of  original.             *)
Lemma L21 : forall (X Y:Prop), And X Y <-> ~~(X /\ Y).
Proof.
    unfold And. intros X Y. split; intros H1 H2; apply H1.
    - intros H3 H4. apply H2. split; assumption.
    - intros [H3 H4]. apply H2; assumption.
Qed.

(* Classical version is equivalent to double negation of  original.             *)
Lemma L22 : forall (X Y:Prop), Or X Y <-> ~~(X \/ Y).
Proof.
    unfold Or. intros X Y. split; intros H1 H2.
    - apply H1; intros H3; apply H2.
        + left. assumption.
        + right. assumption.
    - intros H3. apply H1. intros [H4|H4].
        + apply H2. assumption.
        + apply H3. assumption.
Qed.

(* Classical version is equivalent to double negation of  original.             *)
Lemma L23 : forall (a:Type) (p:a -> Prop),
    Exi p <-> ~~(exists (x:a), p x).
Proof.
    unfold Exi. intros a p. split; intros H1 H2; apply H1.
    - intros x H3. apply H2. exists x. assumption.
    - intros [x H3]. apply (H2 x). assumption.
Qed.

Lemma L24 : forall (X:Prop), Or X (~X).
Proof.
    unfold Or. intros X H1 H2. apply H2. assumption.
Qed.

Lemma L25 : forall (X Y:Prop), ~(And X Y) <-> Or (~X) (~Y).
Proof.
    unfold Or, And. intros X Y. split; intros H1 H2.
    - intros H3. apply H1. intros H4. apply H2. intros H5.
      apply H3. intros H6. apply H4; assumption.
    - apply H2. intros H3 H4. apply H1; intros H5; apply H5; assumption.
Qed.

(* Not much to prove actually, literally the same statements, see L27.          *)
Lemma L26 : forall (X Y:Prop), ~(Or X Y) <-> And (~X) (~Y).
Proof.
    unfold Or, And. intros X Y. split; intros H1 H2; apply H1.
    - intros H3 H4. apply H2; assumption.
    - assumption.
Qed.

Lemma L27 : forall (X Y:Prop), ~(Or X Y) <-> And (~X) (~Y).
Proof.
    unfold Or, And, not. intros X Y. split; auto.
Qed.

Lemma L28 : forall (a:Type) (p:a -> Prop), 
    (forall (x:a), Stable (p x)) -> 
        ~(forall (x:a), p x) <-> Exi (fun x => ~ p x).
Proof.
    unfold Stable, Exi. intros a p H1. split; intros H2 H3; apply H2; intros x.
    - apply H1. intros H4. apply (H3 x). assumption.
    - intros H4. apply H4, H3.
Qed.

Lemma L29 : forall (X Y:Prop), Stable (And X Y).
Proof.
    unfold And, Stable. intros X Y H1 H2. apply H1. intros H3. apply H3. 
    assumption.
Qed.

Lemma L30 : forall (X Y:Prop), Stable (Or X Y).
Proof.
    unfold Or, Stable. intros X Y H1 H2 H3. apply H1. intros H4. apply H4; 
    assumption.
Qed.

Lemma L31 : forall (a:Type) (p:a -> Prop), Stable (Exi p).
Proof.
    unfold Exi, Stable. intros a p H1 H2. apply H1. intros H3. apply H3.
    assumption.
Qed.

