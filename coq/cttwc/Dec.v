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


Definition L12 (b:bool) : {b = true} + {b = false}.
Proof.
    destruct b.
    - left. reflexivity.
    - right. reflexivity.
Defined.

Definition L13 : forall (a:Type) (x y:a),
    (forall (p:a -> Type), p x -> p y -> forall (z:a), p z) 
    ->
    forall (z:a), {z = x} + {z = y}.
Proof.
    intros a x y H z. apply (H (fun z => {z = x} + {z = y})).
    - left. reflexivity.
    - right. reflexivity.
Defined.

Definition L14 : forall (a:Type) (x y:a),
    (forall (z:a), {z = x} + {z = y})
    ->
    forall (p:a -> Type), p x -> p y -> forall (z:a), p z.
Proof.
    intros a x y H p H1 H2 z. destruct (H z) as [H3|H3]; rewrite H3; assumption.
Defined.

Definition EqDecider (a:Type) (f:a -> a -> bool) : Prop :=
    forall (x y:a), x = y <-> f x y = true.
 
Arguments EqDecider {a}.

Definition Discrete (a:Type) : Prop := exists (f:a -> a -> bool), EqDecider f.

Lemma L15 : forall (a:Type), 
    Discrete a <-> exists (q:forall (x y:a), Dec (x = y)), True.
Proof.
    unfold Discrete, EqDecider, Dec. intros a. split.
    - intros [f H1]. assert (forall (x y:a), {x = y} + {x <> y}) as q.
        { intros x y. destruct (f x y) eqn:E.
            { apply H1 in E. left. assumption. }
            { destruct (H1 x y) as [H2 H3]. right. intros H4.
              rewrite H2 in E. inversion E. assumption. }}
      exists q. trivial.
    - intros [q _]. remember (fun x y =>
        match (q x y) with
        | left _    => true
        | right _   => false
        end) as f eqn:E. exists f. intros x y. split; intros H1.
        + rewrite H1, E. destruct (q y y) as [H2|H2].
            { reflexivity. }
            { exfalso. apply H2. reflexivity. } 
        + rewrite E in H1. destruct (q x y) as [H2|H2].
            { assumption. }
            { inversion H1. }
Qed.

Lemma L16 : forall (a b:Type), 
    Discrete a -> Discrete b -> Discrete (a + b).
Proof.

Show.



