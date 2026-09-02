Require Import Logic.Axiom.Extensionality.

Require Import Logic.Rel.R.
Require Import Logic.Rel.Embed.
Require Import Logic.Rel.Composition.

(* The category of relations has coproducts with sum object a + b               *)

(* Injection mappings                                                           *)
Definition inj1 (a b:Type) : R a (a + b) := embed inl.
Definition inj2 (a b:Type) : R b (a + b) := embed inr.

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

(* Arrow needed for coproduct universal property.                               *)
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

(* Existence part of universal property                                         *)
Lemma sum_existence : forall (a b c:Type) (r:R a c) (s:R b c), 
    exists (t:R (a + b) c), t ; inj1 = r /\ t ; inj2 = s.
Proof.
    intros a b c r s. exists (either r s). split.
    - apply either_inj1.
    - apply either_inj2.
Qed.

(* Uniqueness part of universal property                                        *)
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
