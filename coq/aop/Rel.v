Definition R (a b:Type) : Type := a -> b -> Prop.

Axiom Ext : forall (a b:Type) (r s:R a b),
    (forall (x:a) (y:b), r x y <-> s x y) -> r = s.

Inductive func_embed (a b:Type) (f:a -> b) : R a b :=
| mkEmbed : forall (x:a), func_embed a b f x (f x)
.

Arguments func_embed {a} {b}.

Lemma func_embed_charac : forall (a b:Type) (f:a -> b) (x:a) (y:b),
    func_embed f x y <-> f x = y.
Proof.
    intros a b f x y. split; intros H1. 
    - destruct H1. reflexivity.
    - rewrite <- H1. constructor.
Qed.

Definition conv (a b:Type) (r:R a b) : R b a := fun y x => r x y.
Arguments conv {a} {b}.

Lemma conv_charac : forall (a b:Type) (r:R a b) (x:a) (y:b),
    conv r y x <-> r x y.
Proof.
    intros a b r x y. unfold conv. split; auto.
Qed.


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

Definition prj1 (a b:Type) : R (a + b) a := conv inj1.
Definition prj2 (a b:Type) : R (a + b) b := conv inj2.

Arguments prj1 {a} {b}.
Arguments prj2 {a} {b}.

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

Lemma prj1_charac : forall (a b:Type) (x:a + b) (y:a), prj1 x y <-> x = inl y.
Proof.
    intros a b x y. unfold prj1, conv. apply inj1_charac.
Qed.

Lemma prj2_charac : forall (a b:Type) (x:a + b) (y:b), prj2 x y <-> x = inr y.
Proof.
    intros a b x y. unfold prj2, conv. apply inj2_charac.
Qed.

(*
Inductive either (a b c:Type) (r:R a c) (s:R b c) : R (a + b) c := 
| eitherL : forall (x:a) (y:c), r x y -> either a b c r s (inl x) y
| eitherR : forall (x:b) (y:c), s x y -> either a b c r s (inr x) y
.

Arguments either {a} {b} {c}.

Lemma either_charac : forall (a b c:Type) (r:R a c) (s:R b c) (x:a + b) (y:c), 
    either r s x y 
        <-> 
    (exists (x':a), x = inl x' /\ r x' y) \/
    (exists (x':b), x = inr x' /\ s x' y).
Proof.
    intros a b c r s x y. split.
    - intros [x' y' H1|x' y' H1].
        + left. exists x'. split.
            { reflexivity. }
            { assumption. }
        + right. exists x'. split.
            { reflexivity. }
            { assumption. }
    - intros [[x' [H1 H2]]|[x' [H1 H2]]]; rewrite H1; constructor; assumption.
Qed.

Lemma either_inj1 : forall (a b c:Type) (r:R a c) (s:R b c), 
    either r s ; inj1 = r.
Proof.
    intros a b c r s. apply Ext. intros x y. unfold comp. split.
    - intros [[z|z] [H1 H2]].
        + remember (inl z) as z' eqn:E. destruct H1. inversion E. 
          subst. clear E. remember (inl z) as z' eqn:E. destruct H2; inversion E.
          subst. assumption.
        + remember (inr z) as z' eqn:E. destruct H1. inversion E. 
    - intros H1. exists (inl x). split.
        + constructor.
        + constructor. assumption.
Qed.

Lemma either_inj2 : forall (a b c:Type) (r:R a c) (s:R b c), 
    either r s ; inj2 = s.
Proof.
    intros a b c r s. apply Ext. intros x y. unfold comp. split.
    - intros [[z|z] [H1 H2]].
        + remember (inl z) as z' eqn:E. destruct H1. inversion E. 
        + remember (inr z) as z' eqn:E. destruct H1. inversion E. 
          subst. clear E. remember (inr z) as z' eqn:E. destruct H2; inversion E.
          subst. assumption.
    - intros H1. exists (inr x). split.
        + constructor.
        + constructor. assumption.
Qed.

Lemma sum_existence : forall (a b c:Type) (r:R a c) (s:R b c), 
    exists (t:R (a + b) c), t ; inj1 = r /\ t ; inj2 = s.
Proof.
    intros a b c r s. exists (either r s). split.
    - apply either_inj1.
    - apply either_inj2.
Qed.

Lemma sum_uniqueness : forall (a b c:Type) (r s:R (a + b) c),
    r ; inj1 = s ; inj1 ->
    r ; inj2 = s ; inj2 ->
    r = s.
Proof.
    intros a b c r s H1 H2. apply Ext. intros [x|x] y.
    - split; intros H3.    
        + assert (exists z, inj1 x z /\ r z y) as H4.
            { exists (inl x). split.
                { constructor. }
                { assumption. }}
          change ((r ; inj1) x y) in H4. rewrite H1 in H4.
          unfold comp in H4. destruct H4 as [z [H4 H5]]. destruct H4. assumption.
        + assert (exists z, inj1 x z /\ s z y) as H4.
            { exists (inl x). split.
                { constructor. }
                { assumption. }}
          change ((s ; inj1) x y) in H4. rewrite <- H1 in H4.
          unfold comp in H4. destruct H4 as [z [H4 H5]]. destruct H4. assumption.
    - split; intros H3.    
        + assert (exists z, inj2 x z /\ r z y) as H4.
            { exists (inr x). split.
                { constructor. }
                { assumption. }}
          change ((r ; inj2) x y) in H4. rewrite H2 in H4.
          unfold comp in H4. destruct H4 as [z [H4 H5]]. destruct H4. assumption.
        + assert (exists z, inj2 x z /\ s z y) as H4.
            { exists (inr x). split.
                { constructor. }
                { assumption. }}
          change ((s ; inj2) x y) in H4. rewrite <- H2 in H4.
          unfold comp in H4. destruct H4 as [z [H4 H5]]. destruct H4. assumption.
Qed.
*)
