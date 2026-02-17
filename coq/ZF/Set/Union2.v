Require Import ZF.Axiom.Extensionality.
Require Import ZF.Class.Equiv.
Require Import ZF.Class.Small.
Require Import ZF.Class.Union2.
Require Import ZF.Set.Core.
Require Import ZF.Set.Empty.
Require Import ZF.Set.FromClass.
Require Import ZF.Set.Incl.
Require Import ZF.Set.Pair.
Require Import ZF.Set.Single.
Export ZF.Notation.Or.

(* The union of two sets.                                                       *)
Definition union2 (a b:U) : U := fromClass (toClass a :\/: toClass b)
  (IsSmall (toClass a) (toClass b) (SetIsSmall a) (SetIsSmall b)).

(* Notation "a :\/: b" := (union a b)                                           *)
Global Instance SetOr : Or U := { or := union2 }.

(* Characterisation of the elements of the union of two sets.                   *)
Proposition Charac : forall (a b:U),
  forall x, x :< a :\/: b <-> x :< a \/ x :< b.
Proof.
  intros a b x. unfold or, SetOr, union2. split; intros H1.
  - apply FromClass.Charac in H1. apply H1.
  - apply FromClass.Charac, H1.
Qed.

(* The union of two sets is commutative.                                        *)
Proposition Comm : forall (a b:U), a:\/:b = b:\/:a.
Proof.
  intros a b. apply Extensionality. intros x. split;
  intros H1; apply Charac; apply Charac in H1;
  destruct H1 as [H1|H1]; auto.
Qed.

(* The union of two sets is associative.                                        *)
Proposition Assoc : forall (a b c:U), (a:\/:b):\/:c = a:\/:(b:\/:c).
Proof.
  intros a b c. apply Extensionality. intros x. split; intros H1;
  apply Charac in H1; apply Charac; destruct H1 as [H1|H1].
  - apply Charac in H1. destruct H1 as [H1|H1].
    + left. apply H1.
    + right. apply Charac. left. apply H1.
  - right. apply Charac. right. apply H1.
  - left. apply Charac. left. apply H1.
  - apply Charac in H1. destruct H1 as [H1|H1].
    + left. apply Charac. right. apply H1.
    + right. apply H1.
Qed.

(* Union is compatible with inclusion.                                          *)
Proposition InclCompat : forall (a b c d:U),
  a :<=: b -> c :<=: d -> a:\/:c :<=: b:\/:d.
Proof.
  intros a b c d H1 H2 x H3. apply Charac in H3.
  destruct H3 as [H3|H3]; apply Charac.
  - left. apply H1. assumption.
  - right. apply H2. assumption.
Qed.

(* Union is left-compatible with inclusion.                                     *)
Proposition InclCompatL : forall (a b c:U),
  a :<=: b -> a:\/:c :<=: b:\/:c.
Proof.
  intros a b c H1. apply InclCompat.
  - assumption.
  - apply Incl.Refl.
Qed.

(* Union is right-compatible with inclusion.                                    *)
Proposition InclCompatR : forall (a b c:U),
  a :<=: b -> c:\/:a :<=: c:\/:b.
Proof.
  intros a b c H1. apply InclCompat.
  - apply Incl.Refl.
  - assumption.
Qed.

Proposition WhenEqualR : forall (a b:U),
  b = a :\/: b <-> a :<=: b.
Proof.
  intros a b. split; intros H1.
  - intros x H2. rewrite H1. apply Charac. left. apply H2.
  - apply Extensionality. intros x. split; intros H2.
    + apply Charac. right. apply H2.
    + apply Charac in H2. destruct H2 as [H2|H2].
      * apply H1, H2.
      * apply H2.
Qed.

Proposition IsInclL : forall (a b:U), a :<=: a:\/:b.
Proof.
  intros a b x H1. apply Charac. left. apply H1.
Qed.

Proposition IsInclR : forall (a b:U), b :<=: a:\/:b.
Proof.
  intros a b x H1. apply Charac. right. apply H1.
Qed.

Proposition PairAsUnion2 : forall (a b:U),
  :{a,b}: = :{a}: :\/: :{b}:.
Proof.
  intros a b. apply DoubleInclusion. split; intros x H1.
  - apply Pair.Charac in H1. destruct H1 as [H1|H1]; apply Charac.
    + left. apply Single.Charac. assumption.
    + right. apply Single.Charac. assumption.
  - apply Charac in H1. destruct H1 as [H1|H1]; apply Single.Charac in H1.
    + subst. apply Pair.IsInL.
    + subst. apply Pair.IsInR.
Qed.

Proposition IdentityL : forall (a:U),
  :0: :\/: a = a.
Proof.
  intros a. apply DoubleInclusion. split; intros x H1.
  - apply Charac in H1. destruct H1 as [H1|H1]. 2: assumption.
    apply Empty.Charac in H1. contradiction.
  - apply Charac. right. assumption.
Qed.

Proposition IdentityR : forall (a:U),
  a :\/: :0: = a.
Proof.
  intros a. rewrite Comm. apply IdentityL.
Qed.
