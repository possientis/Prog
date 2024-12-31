Require Import ZF.Axiom.Classic.
Require Import ZF.Class.
Require Import ZF.Class.Empty.
Require Import ZF.Class.Small.
Require Import ZF.Core.Equiv.
Require Import ZF.Core.Zero.
Require Import ZF.Set.
Require Import ZF.Set.OrdPair.

(* Predicate expressing the fact that class P has value y when evaluated at a.  *)
Definition IsValueAt (P:Class) (a y:U) : Prop :=
  P :(a,y): /\ (forall y1 y2, P :(a,y1): -> P :(a,y2): -> y1 = y2).

(* Predicate expressing the fact that class P has a value at a.                 *)
Definition HasValueAt (P:Class) (a:U) : Prop := exists y, IsValueAt P a y.

Definition eval (P:Class) (a:U) : Class := fun x =>
  exists y, x :< y /\ IsValueAt P a y.

(* If P has a value at a and y corresponds to a, then eval P a = y.             *)
Proposition WhenHasValue : forall (P:Class) (a y:U),
  HasValueAt P a -> P :(a,y): -> eval P a :~: toClass y.
Proof.
  intros P a y H1 H2 x. split; intros H3.
  - unfold eval in H3. destruct H3 as [y' [H3 H4]]. unfold IsValueAt in H4.
    destruct H4 as [H4 H5].
    assert (y = y') as H6. { apply H5; assumption. } subst. assumption.
  - unfold HasValueAt in H1. destruct H1 as [y' [H1 H4]].
    unfold eval. exists y. split. 1: assumption. unfold IsValueAt.
    split; assumption.
Qed.

(* If P has no value at a then eval P a is the empty class.                     *)
Proposition WhenNotHasValue : forall (P:Class) (a:U),
  ~ HasValueAt P a -> eval P a :~: :0:.
Proof.
  intros P a H1 x. split; intros H2.
  - apply H1. unfold eval in H2. destruct H2 as [y [H2 H3]].
    destruct H3 as [H3 H4]. exists y. split; assumption.
  - apply EmptyCharac in H2. contradiction.
Qed.

Proposition EvalIsSmall : forall (P:Class) (a:U), Small (eval P a).
Proof.
  (* Let P be an arbitrary class. *)
  intros P.

  (* Let a be an arbitrary set. *)
  intros a.

  (* Either P has a value at a or it has not. *)
  assert (HasValueAt P a \/ ~ HasValueAt P a) as H1. { apply LawExcludedMiddle. }

  (* We consider these two cases separately. *)
  destruct H1 as [H1|H1].

  (* So we assume that P as a value at a. *)
  - assert (HasValueAt P a) as A. { apply H1. } clear A.

  (* Let y be a value of P at a. *)
    remember H1 as H2 eqn:E. clear E. destruct H2 as [y H2].
    assert (IsValueAt P a y) as A. { apply H2. } clear A.

  (* In particular we have P (a,y) *)
    destruct H2 as [H2 _].
    assert (P :(a,y):) as A. { apply H2. } clear A.

  (* And it follows that eval P a = y. *)
    assert (eval P a :~: toClass y) as H3. { apply WhenHasValue; assumption. }

  (* Using this equivalence ... *)
    apply SmallEquivCompat with (toClass y). 1: { apply ClassEquivSym, H3. }

  (* We simply need to show that the set y is small *)
    assert (Small (toClass y)) as A. 2: apply A.

  (* Which is clear. *)
    apply SetIsSmall.

  (* We now assume that P as no value at a. *)
  - assert (~ HasValueAt P a) as A. { apply H1. } clear A.

  (* Then eval P a is the empty class. *)
    assert (eval P a :~: :0:) as H2. { apply WhenNotHasValue, H1. }

  (* Using this equivalence ... *)
    apply SmallEquivCompat with :0:. 1: { apply ClassEquivSym, H2. }

  (* We simply need to show that the empty class is small. *)
    assert (Small :0:) as A. 2: apply A.

  (* Which we know is true. *)
    apply EmptyIsSmall.
Qed.
