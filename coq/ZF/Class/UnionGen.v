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

(* Defining the generalized union \/_{x in A} B(x).                             *)
Definition unionGen (A B:Class) : Class
  := :U( fun y => exists x, A x /\ y = B!x ).

(* Notation ":\/:_{ A } B" := (unionGen A B)                                    *)
Global Instance ClassUnionGen : UnionGen Class Class := {unionGen := unionGen }.

Proposition Charac : forall (A B:Class) (y:U),
  :\/:_{A} B y <-> exists x, A x /\ y :< B!x.
Proof.
  intros A B y. split; intros H1.
  - destruct H1 as [b [H1 H2]]. destruct H2 as [x [H2 H3]].
    rewrite H3 in H1. exists x. split; assumption.
  - destruct H1 as [x [H1 H2]]. exists (eval B x). split.
    + assumption.
    + exists x. split. { assumption. } { reflexivity. }
Qed.

Proposition EqualCharac : forall (A B C:Class),
  (forall x, A x -> B!x = C!x)  -> :\/:_{A} B :~: :\/:_{A} C.
Proof.
  intros A B C H1 y. split; intros H2;
  apply Charac in H2; destruct H2 as [x [H2 H3]];
  apply Charac; exists x; split; try assumption.
  - rewrite <- H1; assumption.
  - rewrite H1; assumption.
Qed.

(* The generalized union over a small class is a small class.                   *)
Proposition IsSmall : forall (A B:Class),
  Small A -> Small :\/:_{A} B.
Proof.
  intros A B H1.
  remember (fun x => exists y z, x = :(y,z): /\ z = B!y) as F eqn:H2.
  apply Small.EquivCompat with :U(range (F:|:A)).
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
