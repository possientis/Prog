Require Import ZF.Axiom.Classic.
Require Import ZF.Class.Equiv.
Require Import ZF.Class.Less.
Require Import ZF.Set.Core.
Require Import ZF.Set.Incl.

Export ZF.Notation.Lt.

(* Strict inclusion predicate.                                                  *)
Definition Less (a b:U) : Prop := a :<=: b /\ a <> b.

(* Notation "a :<: b" := (Less a b)                                             *)
Global Instance SetLt : Lt U := { lt := Less }.

Proposition Exists : forall (a b:U),
  a :<: b <-> a :<=: b /\ exists x, x :< b /\ ~ x :< a.
Proof.
  intros a b. split; intros H1.
  - destruct H1 as [H1 H2]. split.
    + apply H1.
    + apply NotForAllNot. intros H3. apply H2. apply DoubleInclusion. split.
      * apply H1.
      * intros x H4. apply DoubleNegation. intros H5. apply (H3 x). split; assumption.
  - destruct H1 as [H1 [x [H2 H3]]]. split.
    + apply H1.
    + intros H4. subst. contradiction.
Qed.

Proposition ToClass : forall (a b:U),
  a :<: b <-> toClass a :<: toClass b.
Proof.
  intros a b. split; intros [H1 H2]; split; try assumption;
  apply NotEqualToClass; assumption.
Qed.

Proposition EqualOrLess : forall (a b:U),
  a :<=: b <-> a = b \/ a :<: b.
Proof.
  intros a b. split; intros H1.
  - apply Class.Less.EquivOrLess in H1. destruct H1 as [H1|H1].
    + left. apply EqualToClass. assumption.
    + right. apply ToClass. assumption.
  - destruct H1 as [H1|H1].
    + subst. apply Incl.Refl.
    + apply H1.
Qed.

Proposition InclLessTran : forall (a b c:U),
  a :<=: b -> b :<: c -> a :<: c.
Proof.
  intros a b c H1 H2. apply ToClass.
  apply Class.Less.InclLessTran with (toClass b). 1: assumption.
  apply ToClass. assumption.
Qed.

Proposition LessInclTran : forall (a b c:U),
  a :<: b -> b :<=: c -> a :<: c.
Proof.
  intros a b c H1 H2. apply ToClass.
  apply Class.Less.LessInclTran with (toClass b). 2: assumption.
  apply ToClass. assumption.
Qed.
