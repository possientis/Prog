Require Import ZF.Class.Equiv.
Require Import ZF.Class.Incl.
Require Import ZF.Class.Ordinal.Core.
Require Import ZF.Class.Ordinal.Omega.
Require Import ZF.Class.Relation.Domain.
Require Import ZF.Class.Relation.Function.
Require Import ZF.Class.Relation.Functional.
Require Import ZF.Class.Relation.Range.
Require Import ZF.Class.Relation.Relation.
Require Import ZF.Set.Core.
Require Import ZF.Set.Empty.
Require Import ZF.Set.Ordinal.Omega.
Require Import ZF.Set.Ordinal.Succ.
Require Import ZF.Set.OrdPair.
Require Import ZF.Set.Relation.EvalOfClass.
Require Import ZF.Set.Union.

Require Import ZF.Notation.Eval.

Module SOO := ZF.Set.Ordinal.Omega.


(* Shifting a function class to the right, with additional value at 0.          *)
Definition shiftR (a:U) (F:Class) := fun x => x = :(:0:,a): \/ exists y z,
  x = :(succ y, z): /\ F :(y,z):.

Proposition Charac2 : forall (F:Class) (a x y:U), x :< :N ->
  shiftR a F :(x,y): <-> (x = :0: /\ y = a) \/ (:0: :< x /\ F :(:U(x),y):).
Proof.
  intros F a x y H1.
  assert (On x) as G1. { apply HasOrdinalElem. assumption. }
  split; intros [H2|H2].
  - left. apply OrdPair.WhenEqual in H2. assumption.
  - right. destruct H2 as [u [v [H2 H3]]].
    apply OrdPair.WhenEqual in H2. destruct H2 as [H2 H4]. subst.
    assert (On u) as H5. {
      apply Succ.IsOrdinalRev, HasOrdinalElem. assumption. }
    rewrite Succ.UnionOf. 2: assumption. split. 2: assumption.
    apply Succ.HasZero. assumption.
  - left. destruct H2 as [H2 H3]. subst. reflexivity.
  - right. destruct H2 as [H2 H3]. exists :U(x), y. split. 2: assumption.
    assert (succ :U(x) = x) as H4. {
      symmetry. apply Succ.WhenSuccessor. 1: assumption.
      apply SOO.IsSuccessor; assumption. }
    rewrite H4. reflexivity.
Qed.

Proposition IsRelation : forall (F:Class) (a:U), Relation (shiftR a F).
Proof.
  intros F a x [H1|H1].
  - exists :0:, a. assumption.
  - destruct H1 as [y [z [H1 _]]]. exists (succ y), z. assumption.
Qed.

Proposition IsFunctional : forall (F:Class) (a:U),
  Functional F -> Functional (shiftR a F).
Proof.
  intros F a H1 y z1 z2 [H2|H2] [H3|H3].
  - apply OrdPair.WhenEqual in H2. destruct H2 as [H2 H4].
    apply OrdPair.WhenEqual in H3. destruct H3 as [H3 H5].
    subst. reflexivity.
  - exfalso. apply OrdPair.WhenEqual in H2. destruct H2 as [H2 H4].
    destruct H3 as [u [v [H3 H5]]].
    apply OrdPair.WhenEqual in H3. destruct H3 as [H3 H6]. subst.
    assert (u :< succ u) as H7. { apply Succ.IsIn. }
    rewrite <- H3 in H7. apply Empty.Charac in H7. contradiction.
  - exfalso. apply OrdPair.WhenEqual in H3. destruct H3 as [H3 H5].
    destruct H2 as [u [v [H2 H4]]].
    apply OrdPair.WhenEqual in H2. destruct H2 as [H2 H6]. subst.
    assert (u :< succ u) as H7. { apply Succ.IsIn. }
    rewrite H3 in H7. apply Empty.Charac in H7. contradiction.
  - destruct H2 as [u1 [v1 [H2 H4]]]. destruct H3 as [u2 [v2 [H3 H5]]].
    apply OrdPair.WhenEqual in H2. destruct H2 as [H2 H6].
    apply OrdPair.WhenEqual in H3. destruct H3 as [H3 H7]. subst.
    assert (u1 = u2) as H8. { apply Succ.Injective. assumption. } subst.
    apply H1 with u2; assumption.
Qed.

Proposition IsFunction : forall (F:Class) (a:U),
  Functional F -> Function (shiftR a F).
Proof.
  intros F a H1. split.
  - apply IsRelation.
  - apply IsFunctional. assumption.
Qed.

Proposition DomainOf : forall (F:Class) (a x:U), x :< :N  ->
  domain (shiftR a F) x <-> x = :0: \/ (:0: :< x /\ domain F :U(x)).
Proof.
  intros F a x H1. split; intros H2.
  - destruct H2 as [y H2]. apply Charac2 in H2. 2: assumption.
    destruct H2 as [[H2 H3]|[H2 H3]].
    + left. assumption.
    + right. split. 1: assumption. exists y. assumption.
  - destruct H2 as [H2|H2].
    + exists a. left. subst. reflexivity.
    + destruct H2 as [H2 [y H3]]. exists y. apply Charac2. 1: assumption.
      right. split; assumption.
Qed.

Proposition EvalZero : forall (F:Class) (a:U), Functional F ->
  (shiftR a F)!:0: = a.
Proof.
  intros F a H1. apply EvalOfClass.Charac.
  - apply IsFunctional. assumption.
  - apply DomainOf. 1: apply SOO.HasZero. left. reflexivity.
  - apply Charac2. 1: apply SOO.HasZero. left. split; reflexivity.
Qed.

Proposition Eval : forall (F:Class) (a x:U),
  Functional F                ->
  x :< :N                     ->
  :0: :< x                    ->
  domain F :U(x)              ->
  (shiftR a F)! x = F!:U(x).
Proof.
  intros F a x H1 H2 H3 H4.
  apply EvalOfClass.Charac.
  - apply IsFunctional. assumption.
  - apply DomainOf. 1: assumption. right. split; assumption.
  - apply Charac2. 1: assumption. right. split. 1: assumption.
    apply EvalOfClass.Satisfies; assumption.
Qed.

Proposition RangeOf : forall (F:Class) (a y:U),
  range (shiftR a F) y <-> y = a \/ range F y.
Proof.
  intros F a y. split; intros H1.
  - destruct H1 as [x [H1|H1]].
    + apply OrdPair.WhenEqual in H1. left. apply H1.
    + destruct H1 as [u [v [H1 H2]]].
      apply OrdPair.WhenEqual in H1. destruct H1 as [H1 H3].
      right. subst. exists u. assumption.
  - destruct H1 as [H1|H1].
    + subst. exists :0:. left. reflexivity.
    + destruct H1 as [x H1]. exists (succ x). right.
      exists x, y. split. 2: assumption. reflexivity.
Qed.

Proposition WhenIntegerDomain : forall (F:Class) (a n:U),
  n :< :N                                   ->
  domain F :~: toClass n                    ->
  domain (shiftR a F) :~: toClass (succ n).
Proof.
  intros F a n H1 H2 x. split; intros H3.
  -
Admitted.



