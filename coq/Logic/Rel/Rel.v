Require Import Logic.Axiom.Extensionality.

Require Import Logic.Rel.R.
Require Import Logic.Rel.Id.
Require Import Logic.Rel.Converse.
Require Import Logic.Rel.Intersect.
Require Import Logic.Rel.Composition.

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

Lemma inj1_prj1 : forall (a b:Type), inj1 = conv (@prj1 a b).
Proof.
    intros a b. apply Ext. intros x y. unfold conv. split; intros H1.
    - apply prj1_charac. apply inj1_charac in H1. assumption.
    - apply inj1_charac. apply prj1_charac in H1. assumption.
Qed.

Lemma prj1_inj1 : forall (a b:Type), prj1 = conv (@inj1 a b).
Proof.
    intros a b. apply Ext. intros x y. unfold conv. split; intros H1.
    - apply prj1_charac. apply inj1_charac in H1. assumption.
    - apply inj1_charac. apply prj1_charac in H1. assumption.
Qed.

Lemma inj2_prj2 : forall (a b:Type), inj2 = conv (@prj2 a b).
Proof.
    intros a b. apply Ext. intros x y. unfold conv. split; intros H1.
    - apply prj2_charac. apply inj2_charac in H1. assumption.
    - apply inj2_charac. apply prj2_charac in H1. assumption.
Qed.

Lemma prj2_inj2 : forall (a b:Type), prj2 = conv (@inj2 a b).
Proof.
    intros a b. apply Ext. intros x y. unfold conv. split; intros H1.
    - apply prj2_charac. apply inj2_charac in H1. assumption.
    - apply inj2_charac. apply prj2_charac in H1. assumption.
Qed.


Inductive either (a b c:Type) (r:R a c) (s:R b c) : R (a + b) c := 
| eitherL : forall (x:a) (y:c), r x y -> either a b c r s (inl x) y
| eitherR : forall (x:b) (y:c), s x y -> either a b c r s (inr x) y
.

Arguments either {a} {b} {c}.

Inductive split (a b c:Type) (r:R a b) (s:R a c) : R a (b + c) :=
| splitL : forall (x:a) (y:b), r x y -> split a b c r s x (inl y)
| splitR : forall (x:a) (y:c), s x y -> split a b c r s x (inr y)
.

Arguments split {a} {b} {c}.

Lemma either_split : forall (a b c:Type) (r:R a c) (s:R b c), 
    either r s = conv (split (conv r) (conv s)).
Proof.
    intros a b c r s. apply Ext. intros x y. unfold conv. split; intros H1;
    destruct H1 as [x y H1|x y H1]; constructor; assumption.
Qed.

Lemma split_either : forall (a b c:Type) (r:R a b) (s:R a c), 
    split r s = conv (either (conv r) (conv s)).
Proof.
    intros a b c r s. apply Ext. intros x y. unfold conv. split; intros H1;
    destruct H1 as [x y H1|x y H1]; constructor; assumption.
Qed.

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

Lemma split_charac : forall (a b c:Type) (r:R a b) (s:R a c) (x:a) (y:b + c),
    split r s x y
        <->
    (exists (y':b), y = inl y' /\ r x y') \/
    (exists (y':c), y = inr y' /\ s x y').
Proof.
    intros a b c r s x y. split.
    - intros [x' y' H1|x' y' H1].
        + left. exists y'. split.
            { reflexivity. }
            { assumption. }
        + right. exists y'. split.
            { reflexivity. }
            { assumption. }

    - intros [[y' [H1 H2]]|[y' [H1 H2]]]; rewrite H1; constructor; assumption.
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


Lemma split_prj1 : forall (a b c:Type) (r:R a b) (s:R a c),
    prj1 ; split r s = r.
Proof.
    intros a b c r s. apply Ext. intros x y. unfold comp. split.
    - intros [[z|z] [H1 H2]]. 
        + remember (inl z) as z' eqn:E. destruct H1; inversion E.
          subst. clear E. remember (inl z) as z' eqn:E. 
          destruct H2. inversion E. subst. assumption.
        + remember (inr z) as z' eqn:E. destruct H1; inversion E.
          subst. clear E. remember (inr z) as z' eqn:E. 
          destruct H2. inversion E.
    - intros H1. exists (inl y). split.
        + constructor. assumption.
        + constructor.
Qed.

Lemma split_prj2 : forall (a b c:Type) (r:R a b) (s:R a c),
    prj2 ; split r s = s.
Proof.
    intros a b c r s. apply Ext. intros x y. unfold comp. split.
    - intros [[z|z] [H1 H2]]. 
        + remember (inl z) as z' eqn:E. destruct H1; inversion E.
          subst. clear E. remember (inl z) as z' eqn:E. destruct H2.
          inversion E.
        + remember (inr z) as z' eqn:E. destruct H1; inversion E.
          subst. clear E. remember (inr z) as z' eqn:E. destruct H2.
          inversion E. subst. assumption.
    - intros H1. exists (inr y). split.
        + constructor. assumption.
        + constructor.
Qed.

Lemma sum_existence : forall (a b c:Type) (r:R a c) (s:R b c), 
    exists (t:R (a + b) c), t ; inj1 = r /\ t ; inj2 = s.
Proof.
    intros a b c r s. exists (either r s). split.
    - apply either_inj1.
    - apply either_inj2.
Qed.

Lemma prd_existence : forall (a b c:Type) (r:R a b) (s:R a c),
    exists (t:R a (b + c)), prj1 ; t = r /\ prj2 ; t = s.
Proof.
    intros a b c r s. exists (split r s). split.
    - apply split_prj1.
    - apply split_prj2.
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

Lemma prd_uniqueness : forall (a b c:Type) (r s:R a (b + c)),
    prj1 ; r = prj1 ; s ->
    prj2 ; r = prj2 ; s ->
    r = s.
Proof.
    intros a b c r s H1 H2. apply Ext. intros x [y|y].
    - split; intros H3.
        + assert (exists z, r x z /\ prj1 z y) as H4.
            { exists (inl y). split.
                { assumption. }
                { constructor. }}
          change ((prj1 ; r) x y) in H4. rewrite H1 in H4.
          unfold comp in H4. destruct H4 as [z [H4 H5]]. destruct H5. assumption.
        + assert (exists z, s x z /\ prj1 z y) as H4.
            { exists (inl y). split.
                { assumption. }
                { constructor. }}
          change ((prj1 ; s) x y) in H4. rewrite <- H1 in H4.
          unfold comp in H4. destruct H4 as [z [H4 H5]]. destruct H5. assumption.
    - split; intros H3.
        + assert (exists z, r x z /\ prj2 z y) as H4.
            { exists (inr y). split.
                { assumption. }
                { constructor. }}
          change ((prj2 ; r) x y) in H4. rewrite H2 in H4.
          unfold comp in H4. destruct H4 as [z [H4 H5]]. destruct H5. assumption.
        + assert (exists z, s x z /\ prj2 z y) as H4.
            { exists (inr y). split.
                { assumption. }
                { constructor. }}
          change ((prj2 ; s) x y) in H4. rewrite <- H2 in H4.
          unfold comp in H4. destruct H4 as [z [H4 H5]]. destruct H5. assumption.
Qed.

Inductive Void : Type :=.

Notation "0" := (Void) : Rel_scope.

Open Scope Rel_scope.

Definition initial (a:Type) : R 0 a := fun x y => False.

Arguments initial {a}.

Definition terminal (a:Type) : R a 0 := fun x y => False.

Arguments terminal {a}.

Lemma initial_existence : forall (a:Type), exists (r:R 0 a), True.
Proof.
    intros a. exists initial. trivial.
Qed.

Lemma initial_uniqueness : forall (a:Type) (r s:R 0 a), r = s.
Proof.
    intros a r s. apply Ext. intros x y. split; intros H1; inversion x.
Qed.

Lemma terminal_existence : forall (a:Type), exists (r:R a 0), True.
Proof.
    intros a. exists terminal. trivial.
Qed.

Lemma terminal_uniqueness : forall (a:Type) (r s:R a 0), r = s.
Proof.
    intros a r s. apply Ext. intros x y. split; intros H1; inversion y.
Qed.

