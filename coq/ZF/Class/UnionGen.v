Require Import ZF.Class.Equiv.
Require Import ZF.Class.Relation.Range.
Require Import ZF.Class.Relation.Restrict.
Require Import ZF.Class.Small.
Require Import ZF.Class.Union.
Require Import ZF.Set.Core.
Require Import ZF.Set.OrdPair.
Require Import ZF.Set.Relation.EvalOfClass.

Require Import ZF.Notation.UnionGen.
Export ZF.Notation.UnionGen.

(* Defining the generalized union \/_{x in P} Q(x).                             *)
Definition unionGen (P Q:Class) : Class
  := :U( fun y => exists x, P x /\ y = Q!x ).

(* Notation ":\/:_{ P } Q" := (unionGen P Q)                                    *)
Global Instance ClassUnionGen : UnionGen Class Class := {unionGen := unionGen }.

Proposition Charac : forall (P Q:Class) (y:U),
  :\/:_{P} Q y <-> exists x, P x /\ y :< Q!x.
Proof.
  intros P Q y. split; intros H1.
  - destruct H1 as [q [H1 H2]]. destruct H2 as [x [H2 H3]].
    rewrite H3 in H1. exists x. split; assumption.
  - destruct H1 as [x [H1 H2]]. exists (eval Q x). split.
    + assumption.
    + exists x. split. { assumption. } { reflexivity. }
Qed.

Proposition IsSmall : forall (P Q:Class),
  Small P -> Small :\/:_{P} Q.
Proof.
  intros P Q H1.
  remember (fun x => exists y z, x = :(y,z): /\ z = Q!y) as F eqn:H2.
  apply Small.EquivCompat with :U(range (F:|:P)).
  - apply Union.EquivCompat. intros z. split; intros H3.
    + destruct H3 as [y H3]. apply Restrict.Charac2 in H3.
      destruct H3 as [H3 H4]. exists y. split. 1: assumption.
      rewrite H2 in H4. destruct H4 as [y' [z' [H4 H5]]].
      apply OrdPair.WhenEqual in H4. destruct H4 as [H4 H6].
      subst. reflexivity.
    + destruct H3 as [y [H3 H4]]. exists y. apply Restrict.Charac2.
      split. 1: assumption. rewrite H2. exists y. exists z.
      split. 2: assumption. reflexivity.
  - apply Union.IsSmall, Range.IsSmall, Restrict.IsSmall. 2: assumption.
    intros x y z H3 H4. rewrite H2 in H3. rewrite H2 in H4.
    destruct H3 as [x1 [y' [H3 H5]]]. destruct H4 as [x2 [z' [H4 H6]]].
    apply OrdPair.WhenEqual in H3. destruct H3 as [H3 H7].
    apply OrdPair.WhenEqual in H4. destruct H4 as [H4 H8].
    subst. reflexivity.
Qed.
