Require Import ZF.Axiom.Classic.
Require Import ZF.Axiom.Extensionality.
Require Import ZF.Class.
Require Import ZF.Class.Incl.
Require Import ZF.Set.

Export ZF.Notation.Leq.
Export ZF.Notation.Lt.

(* Inclusion predicate between two sets.                                        *)
Definition Incl (a b:U) : Prop := Class.Incl.Incl (toClass a) (toClass b).

(* Notation "a :<=: b" := (Incl a b)                                            *)
Global Instance SetLeq : Leq U := { leq := Incl }.

(* Strict inclusion predicate.                                                  *)
Definition StrictIncl (a b:U) : Prop := a :<=: b /\ a <> b.

(* Notation "a :<: b" := (InclStrict a b)                                       *)
Global Instance SetLt : Lt U := { lt := StrictIncl }.

(* Two sets are equal if and only if they are subsets of each other.            *)
Proposition DoubleInclusion : forall (a b:U),
  a = b <-> a :<=: b /\ b :<=: a.
Proof.
  intros a b. unfold Incl. split.
  - intros H1. split; intros x Hx.
    + rewrite <- H1. apply Hx.
    + rewrite H1. apply Hx.
  - intros [H1 H2]. apply Extensionality. intros x. split.
    + apply H1.
    + apply H2.
Qed.

(* The inclusion relation is reflexive.                                         *)
Proposition InclRefl : forall (a:U), a :<=: a.
Proof.
  intros a x. auto.
Qed.

(* The inclusion relation is anti-symmetric.                                    *)
Proposition InclAnti : forall (a b:U),
  a :<=: b -> b :<=: a -> a = b.
Proof.
  intros a b H1 H2. apply DoubleInclusion. split; assumption.
Qed.

(* The inclusion relation is transitive.                                        *)
Proposition InclTran : forall (a b c:U),
  a :<=: b -> b :<=: c -> a :<=: c.
Proof.
  intros a b c H1 H2 x H3. apply H2, H1, H3.
Qed.

Proposition StrictInclExists : forall (a b:U),
  a :<: b <-> a :<=: b /\ exists x, x :< b /\ ~ x :< a.
Proof.
  intros a b. split; intros H1.
  - unfold StrictIncl in H1. destruct H1 as [H1 H2]. split.
    + apply H1.
    + apply NotForAllNot. intros H3. apply H2. apply DoubleInclusion. split.
      * apply H1.
      * intros x H4. apply DoubleNegation. intros H5. apply (H3 x). split; assumption.
  - destruct H1 as [H1 [x [H2 H3]]]. unfold StrictIncl. split.
    + apply H1.
    + intros H4. subst. contradiction.
Qed.

Proposition StrictInclFromClass : forall (a b:U),
  a :<: b <-> toClass a :<: toClass b.
Proof.
  intros a b. split; intros [H1 H2]; split; try assumption;
  apply NotEquivSetNotEqual; assumption.
Qed.

Proposition EqualOrStrictIncl : forall (a b:U),
  a :<=: b <-> a = b \/ a :<: b.
Proof.
  intros a b. split; intros H1.
  - apply EquivOrStrictIncl in H1. destruct H1 as [H1|H1].
    + left. apply EquivSetEqual. assumption.
    + right. apply StrictInclFromClass. assumption.
  - destruct H1 as [H1|H1].
    + subst. apply InclRefl.
    + apply H1.
Qed.

Proposition InclStrictInclTran : forall (a b c:U),
  a :<=: b -> b :<: c -> a :<: c.
Proof.
  intros a b c H1 H2. apply StrictInclFromClass.
  apply Class.Incl.InclStrictInclTran with (toClass b). 1: assumption.
  apply StrictInclFromClass. assumption.
Qed.

Proposition StrictInclInclTran : forall (a b c:U),
  a :<: b -> b :<=: c -> a :<: c.
Proof.
  intros a b c H1 H2. apply StrictInclFromClass.
  apply Class.Incl.StrictInclInclTran with (toClass b). 2: assumption.
  apply StrictInclFromClass. assumption.
Qed.
