Require Import Logic.Axiom.Extensionality.

Require Import Logic.Rel.R.
Require Import Logic.Rel.Sum.
Require Import Logic.Rel.Converse.
Require Import Logic.Rel.Composition.

(* The category of relations has products with product object a + b             *)

(* Projection mappings, defined in terms of injection mapping for sum.          *)
Definition prj1 (a b:Type) : R (a + b) a := conv inj1.
Definition prj2 (a b:Type) : R (a + b) b := conv inj2.

Arguments prj1 {a} {b}.
Arguments prj2 {a} {b}.

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

Lemma inj2_prj2 : forall (a b:Type), inj2 = conv (@prj2 a b).
Proof.
    intros a b. apply Ext. intros x y. unfold conv. split; intros H1.
    - apply prj2_charac. apply inj2_charac in H1. assumption.
    - apply inj2_charac. apply prj2_charac in H1. assumption.
Qed.

(* True by definition                                                           *)
Lemma prj1_inj1 : forall (a b:Type), prj1 = conv (@inj1 a b).
Proof.
    intros a b. reflexivity.
Qed.

(* True by definition                                                           *)
Lemma prj2_inj2 : forall (a b:Type), prj2 = conv (@inj2 a b).
Proof.
    intros a b. reflexivity.
Qed.

(* Arrow needed for product universal property.                                 *)
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

(* Existence part of universal property                                         *)
Lemma prd_existence : forall (a b c:Type) (r:R a b) (s:R a c),
    exists (t:R a (b + c)), prj1 ; t = r /\ prj2 ; t = s.
Proof.
    intros a b c r s. exists (split r s). split.
    - apply split_prj1.
    - apply split_prj2.
Qed.

(* Uniqueness part of universal property                                        *)
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
