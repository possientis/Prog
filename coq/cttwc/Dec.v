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

Definition L7 : forall (X Y:Prop), (X <-> Y) -> Dec X -> Dec Y.
Proof.
    unfold Dec. intros X Y [H1 H2] [H3|H3].
    - left. apply H1. assumption.
    - right. intros H4. apply H3, H2. assumption.
Defined.

Definition Decider (a:Type) (f:a -> bool) (p:a -> Prop) : Prop :=
    forall (x:a), p x <-> f x = true.

Arguments Decider {a}.

Definition toBool(a:Type)(p:a -> Prop)(q:forall (x:a), Dec (p x))(x:a) : bool.
Proof.
    unfold Dec in q. destruct (q x) as [H1|H1].
    - exact true.
    - exact false.
Defined.

Arguments toBool {a} {p}.

Lemma L8 : forall (a:Type) (p:a -> Prop) (q:forall (x:a), Dec (p x)),
   Decider (toBool q) p.
Proof.
    unfold Decider, toBool. intros a p q. intros x. 
    destruct (q x) as [H1|H1]; split; intros  H2.
    - reflexivity.
    - assumption.
    - apply H1 in H2. contradiction.
    - inversion H2.
Qed.

Definition toDec(a:Type)(p:a -> Prop)(f:a -> bool)(q:Decider f p)(x:a):Dec (p x).
Proof.
    unfold Dec. unfold Decider in q. destruct (f x) eqn:E.
    - left. apply q. assumption.
    - right. intros H1. apply (q x) in H1. rewrite E in H1. inversion H1.
Qed.

Definition L9 : forall (X Y:Prop), {X} + {Y} -> X \/ Y.
Proof.
    intros X Y [H1|H1].
    - left. assumption.
    - right. assumption.
Qed.


Lemma L10 : forall (X Y:Prop), (exists (q:{X} + {Y}), True) <-> X \/ Y.
Proof.
    intros X Y. split.
    - intros [[q|q] _].
        + left. assumption.
        + right. assumption.
    - intros [q|q].
        + exists (left q). trivial.
        + exists (right q). trivial.
Qed.

Definition L11 (a:Type) (p:a -> Prop) :
    (forall (x:a), Dec (p x)) -> forall (x:a), p x \/ ~ p x.
Proof.
    unfold Dec. intros q x. destruct (q x) as [H1|H1].
    - left. assumption.
    - right. assumption.
Defined.

