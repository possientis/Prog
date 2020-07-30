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

Definition L4 (X:Prop) (b:bool) (p:X <-> b = true) : { X } + {~ X}.
Proof.
    destruct p as [H1 H2]. destruct b.
    - left. apply H2. reflexivity.
    - right.  intros H3. apply H1 in H3. inversion H3.
Defined.

Arguments L4 {X} {b}.

Lemma L5 : forall (a:Type) (p:a -> Prop),
    Decidable p <-> exists (q:forall (x:a), {p x} + {~p x}), True.
Proof.
    unfold Decidable, Decider. intros a p. split.
    - intros [f H1]. exists (fun (x:a) => L4 (H1 x)). trivial.
    - intros [q _ ]. exists (fun (x:a) => 
        match q x with 
        | left _  => true 
        | right _ => false
        end).
      intros x. destruct (q x) as [H1|H1].
        + split.
            { intros. reflexivity. }
            { intros. assumption. }
        + split.
            { intros H2. exfalso. apply H1. assumption. }
            { intros H2. inversion H2. }
Qed.


Lemma L6 : forall (a:Type) (p:a -> Prop), 
    Decidable p -> Decidable (fun x => ~p x).
Proof.
    intros a p. unfold Decidable, Decider. intros [f H1].
    exists (fun x => negb (f x)). intros x. unfold negb. split; intros H2.
    - destruct (f x) eqn:E. 
        + apply H1 in E. apply H2 in E. contradiction.
        + reflexivity.
    - destruct (f x) eqn:E. 
        + inversion H2.
        + intros H3. apply H1 in H3. rewrite H3 in E. inversion E.
Qed.
    
Lemma L7 : forall (a:Type) (p q:a -> Prop),
    Decidable p -> Decidable q -> Decidable (fun x => p x -> q x).
Proof.
    intros a p q. unfold Decidable, Decider. intros [f1 H1] [f2 H2].
    exists (fun x => orb (negb (f1 x)) (f2 x)). intros x. unfold negb, orb. 
    split; intros H3.
    - destruct (f1 x) eqn:E1; destruct (f2 x) eqn:E2.
        + reflexivity.
        + apply H1 in E1. apply H3 in E1. apply H2 in E1. rewrite E1 in E2.
          inversion E2.
        + reflexivity.
        + reflexivity.
    - destruct (f1 x) eqn:E1; destruct (f2 x) eqn:E2; intros H4; apply H2. 
        + assumption.
        + inversion H3.
        + assumption.
        + apply H1 in H4. rewrite E1 in H4. inversion H4.
Qed.

Lemma L8 : forall (a:Type) (p q:a -> Prop),
    Decidable p -> Decidable q -> Decidable (fun x => p x /\ q x).
Proof.
    intros a p q. unfold Decidable, Decider. intros [f1 H1] [f2 H2].
    exists (fun x => andb (f1 x) (f2 x)). intros x. unfold andb. 
    split; intros H3.
    - destruct (f1 x) eqn:E1; destruct (f2 x) eqn:E2.
        + reflexivity.
        + destruct H3 as [H3 H4]. apply H2 in H4. rewrite E2 in H4. inversion H4.
        + destruct H3 as [H3 H4]. apply H1 in H3. rewrite E1 in H3. inversion H3.
        + destruct H3 as [H3 H4]. apply H1 in H3. rewrite E1 in H3. inversion H3.
    - destruct (f1 x) eqn:E1; destruct (f2 x) eqn:E2; split.
        + apply H1. assumption.
        + apply H2. assumption.
        + inversion H3.
        + inversion H3.
        + inversion H3.
        + apply H2. assumption.
        + inversion H3.
        + inversion H3.
Qed.


Lemma L9 : forall (a:Type) (p q:a -> Prop),
    Decidable p -> Decidable q -> Decidable (fun x => p x \/ q x).
Proof.
    intros a p q. unfold Decidable, Decider. intros [f1 H1] [f2 H2].
    exists (fun x => orb (f1 x) (f2 x)). intros x. unfold orb. 
    split; intros H3.
    - destruct (f1 x) eqn:E1; destruct (f2 x) eqn:E2.
        + reflexivity.
        + reflexivity.
        + reflexivity.
        + destruct H3 as [H3|H3].
            { apply H1 in H3. rewrite E1 in H3. inversion H3. }
            { apply H2 in H3. rewrite E2 in H3. inversion H3. }
    - destruct (f1 x) eqn:E1; destruct (f2 x) eqn:E2.
        + left. apply H1. assumption.
        + left. apply H1. assumption.
        + right. apply H2. assumption.
        + inversion H3.
Qed.

Lemma L10 : forall (a:Type) (p q:a -> Prop) (f:a -> bool),
    (forall (x:a), p x <-> q x) -> Decider f p -> Decider f q.
Proof.
    unfold Decider. intros a p q f H1 H2 x. split; intros H3.
    - apply H2, H1. assumption.
    - apply H1, H2. assumption.
Qed. 

Lemma L11 : forall (a:Type) (p:a -> Prop),
    Decidable p -> forall (x:a), p x \/ ~p x.
Proof.
    intros a p. unfold Decidable, Decider. intros [f H1] x. destruct (f x) eqn:E.
    - left. apply H1. assumption.
    - right. intros H2. apply H1 in H2. rewrite E in H2. inversion H2.
Qed.


Lemma L12 : forall (a:Type) (p q:a -> Prop) (f:a -> bool),
    Decider f p -> Decider f q -> forall (x:a), p x <-> q x.
Proof.
    unfold Decider. intros a p q f H1 H2 x. split; intros H3.
    - apply H2, H1. assumption.
    - apply H1, H2. assumption.
Qed.
