Require Import ZF.Axiom.Extensionality.
Require Import ZF.Class.
Require Import ZF.Class.Small.
Require Import ZF.Class.Union2.
Require Import ZF.Set.
Require Import ZF.Set.Empty.
Require Import ZF.Set.FromClass.
Require Import ZF.Set.Incl.
Require Import ZF.Set.Pair.
Require Import ZF.Set.Singleton.
Export ZF.Notation.Or.

(* The union of two sets.                                                       *)
Definition union2 (a b:U) : U := fromClass (toClass a :\/: toClass b)
  (Union2IsSmall (toClass a) (toClass b) (SetIsSmall a) (SetIsSmall b)).

(* Notation "a :\/: b" := (union a b)                                           *)
Global Instance SetOr : Or U := { or := union2 }.

(* Characterisation of the elements of the union of two sets.                   *)
Proposition Union2Charac : forall (a b:U),
  forall x, x :< a:\/:b <-> x :< a \/ x :< b.
Proof.
  intros a b x. unfold or, SetOr, union2. split; intros H1.
  - apply FromClassCharac in H1.
    apply (proj1 (Class.Union2.Union2Charac _ _ _)) in H1. apply H1.
  - apply FromClassCharac, Class.Union2.Union2Charac, H1.
Qed.

(* The union of two sets is commutative.                                        *)
Proposition Union2Comm : forall (a b:U), a:\/:b = b:\/:a.
Proof.
  intros a b. apply Extensionality. intros x. split;
  intros H1; apply Union2Charac; apply Union2Charac in H1;
  destruct H1 as [H1|H1]; auto.
Qed.

(* The union of two sets is associative.                                        *)
Proposition Union2Assoc : forall (a b c:U), (a:\/:b):\/:c = a:\/:(b:\/:c).
Proof.
  intros a b c. apply Extensionality. intros x. split; intros H1;
  apply Union2Charac in H1; apply Union2Charac; destruct H1 as [H1|H1].
  - apply Union2Charac in H1. destruct H1 as [H1|H1].
    + left. apply H1.
    + right. apply Union2Charac. left. apply H1.
  - right. apply Union2Charac. right. apply H1.
  - left. apply Union2Charac. left. apply H1.
  - apply Union2Charac in H1. destruct H1 as [H1|H1].
    + left. apply Union2Charac. right. apply H1.
    + right. apply H1.
Qed.

(* Union is compatible with inclusion.                                          *)
Proposition Union2InclCompat : forall (a b c d:U),
  a :<=: b -> c :<=: d -> a:\/:c :<=: b:\/:d.
Proof.
  intros a b c d H1 H2 x H3. apply Union2Charac in H3.
  destruct H3 as [H3|H3]; apply Union2Charac.
  - left. apply H1. assumption.
  - right. apply H2. assumption.
Qed.

(* Union is left-compatible with inclusion.                                     *)
Proposition Union2InclCompatL : forall (a b c:U),
  a :<=: b -> a:\/:c :<=: b:\/:c.
Proof.
  intros a b c H1. apply Union2InclCompat.
  - assumption.
  - apply InclRefl.
Qed.

(* Union is right-compatible with inclusion.                                    *)
Proposition Union2InclCompatR : forall (a b c:U),
  a :<=: b -> c:\/:a :<=: c:\/:b.
Proof.
  intros a b c H1. apply Union2InclCompat.
  - apply InclRefl.
  - assumption.
Qed.

Proposition Union2EqualIncl : forall (a b:U),
  b = a :\/: b <-> a :<=: b.
Proof.
  intros a b. split; intros H1.
  - intros x H2. rewrite H1. apply Union2Charac. left. apply H2.
  - apply Extensionality. intros x. split; intros H2.
    + apply Union2Charac. right. apply H2.
    + apply Union2Charac in H2. destruct H2 as [H2|H2].
      * apply H1, H2.
      * apply H2.
Qed.

Proposition Union2InclL : forall (a b:U), a :<=: a:\/:b.
Proof.
  intros a b x H1. apply Union2Charac. left. apply H1.
Qed.

Proposition Union2InclR : forall (a b:U), b :<=: a:\/:b.
Proof.
  intros a b x H1. apply Union2Charac. right. apply H1.
Qed.

Proposition PairAsUnion2 : forall (a b:U),
  :{a,b}: = :{a}: :\/: :{b}:.
Proof.
  intros a b. apply DoubleInclusion. split; intros x H1.
  - apply PairCharac in H1. destruct H1 as [H1|H1]; apply Union2Charac.
    + left. apply SingleCharac. assumption.
    + right. apply SingleCharac. assumption.
  - apply Union2Charac in H1. destruct H1 as [H1|H1]; apply SingleCharac in H1.
    + subst. apply PairInL.
    + subst. apply PairInR.
Qed.

Proposition Union2IdentityL : forall (a:U),
  :0: :\/: a = a.
Proof.
  intros a. apply DoubleInclusion. split; intros x H1.
  - apply Union2Charac in H1. destruct H1 as [H1|H1]. 2: assumption.
    apply EmptyCharac in H1. contradiction.
  - apply Union2Charac. right. assumption.
Qed.

Proposition Union2IdentityR : forall (a:U),
  a :\/: :0: = a.
Proof.
  intros a. rewrite Union2Comm. apply Union2IdentityL.
Qed.
