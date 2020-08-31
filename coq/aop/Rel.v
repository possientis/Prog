Definition R (a b:Type) : Type := a -> b -> Prop.

Axiom Ext : forall (a b:Type) (r s:R a b),
    (forall (x:a) (y:b), r x y <-> s x y) -> r = s.

Inductive func_embed (a b:Type) (f:a -> b) : R a b :=
| mkEmbed : forall (x:a), func_embed a b f x (f x)
.

Arguments func_embed {a} {b}.


Inductive id (a:Type) : R a a :=
| refl : forall (x:a), id a x x
.

Arguments id {a}.

Lemma id_charac : forall (a:Type) (x y:a),
    id x y <-> x = y.
Proof.
    intros a x y. split; intros H1.
    - destruct H1. reflexivity.
    - rewrite H1. constructor.
Qed.

Definition comp (a b c:Type) (s:R b c) (r:R a b) : R a c :=
    fun (x:a) (z:c) => exists (y:b), r x y /\ s y z.

Arguments comp {a} {b} {c}.

Notation "s ; r" := (comp s r) 
    (at level 60, right associativity) : Rel_scope.

Open Scope Rel_scope.

Lemma id_left : forall (a b:Type) (r:R a b), r ; id = r.
Proof.
    intros a b r. apply Ext. intros x y. unfold comp. split.
    - intros [z [H1 H2]]. destruct H1. assumption.
    - intros H1. exists x. split.
        + constructor.
        + assumption.
Qed.

Lemma id_right : forall (a b:Type) (r:R a b), id ; r = r.
Proof.
    intros a b r. apply Ext. intros x y. unfold comp. split.
    - intros [z [H1 H2]]. destruct H2 as [y]. assumption.
    - intros H1. exists y. split.
        + assumption.
        + constructor.
Qed.

Lemma comp_assoc : forall (a b c d:Type) (r:R a b) (s:R b c) (t:R c d),
    (t ; s) ; r = t ; (s ; r).
Proof.
    intros a b c d r s t. apply Ext. intros x y. unfold comp. split.
    - intros [x' [H1 [y' [H2 H3]]]]. exists y'. split.
        + exists x'. split; assumption.
        + assumption.
    - intros [y' [[x' [H1 H2]] H3]]. exists x'. split.
        + assumption.
        + exists y'. split; assumption.
Qed.

Definition inj1 (a b:Type) : R a (a + b) := func_embed inl.
Definition inj2 (a b:Type) : R b (a + b) := func_embed inr.

Arguments inj1 {a} {b}.
Arguments inj2 {a} {b}.

Lemma inj1_charac : forall (a b:Type) (x:a) (y:a + b), inj1 x y <-> y = inl x.
Proof.
    intros a b x y. unfold inj1. split; intros H1.
    - destruct H1. reflexivity.
    - rewrite H1. constructor.
Qed.

Lemma inj2_charac : forall (a b:Type) (x:b) (y:a + b), inj2 x y <-> y = inr x.
Proof.
    intros a b x y. unfold inj2. split; intros H1.
    - destruct H1. reflexivity.
    - rewrite H1. constructor.
Qed.
