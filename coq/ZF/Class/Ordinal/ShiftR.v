Require Import ZF.Class.Equiv.
Require Import ZF.Class.Incl.
Require Import ZF.Class.Ordinal.Core.
Require Import ZF.Class.Ordinal.Omega.
Require Import ZF.Class.Ordinal.OrdFun.
Require Import ZF.Class.Relation.Domain.
Require Import ZF.Class.Relation.Function.
Require Import ZF.Class.Relation.Functional.
Require Import ZF.Class.Relation.Range.
Require Import ZF.Class.Relation.Relation.
Require Import ZF.Set.Core.
Require Import ZF.Set.Empty.
Require Import ZF.Set.Ordinal.Core.
Require Import ZF.Set.Ordinal.Omega.
Require Import ZF.Set.Ordinal.Succ.
Require Import ZF.Set.Ordinal.UnionOf.
Require Import ZF.Set.OrdPair.
Require Import ZF.Set.Relation.EvalOfClass.
Require Import ZF.Set.Union.

Require Import ZF.Notation.Eval.

Module SOC := ZF.Set.Ordinal.Core.
Module SOO := ZF.Set.Ordinal.Omega.
Module COC := ZF.Class.Ordinal.Core.


(* Shifting a function class to the right, with additional value at 0.          *)
Definition shiftR (a:U) (F:Class) := fun x => x = :(:0:,a): \/ exists y z,
  x = :(succ y, z): /\ F :(y,z):.

Proposition Charac2 : forall (F:Class) (a x y:U), domain F :<=: toClass :N ->
  shiftR a F :(x,y): <->
  x = :0: /\ y = a \/ :0: :< x /\ x :< :N /\ F :(:U(x),y):.
Proof.
  intros F a x y H1. split; intros [H2|H2].
  - left. apply OrdPair.WhenEqual in H2. assumption.
  - right. destruct H2 as [u [v [H2 H3]]].
    apply OrdPair.WhenEqual in H2. destruct H2 as [H2 H4]. subst.
    assert (u :< :N) as G1. { apply H1. exists v. assumption. }
    assert (succ u :< :N) as G2. { apply Omega.HasSucc. assumption. }
    assert (On u) as G3. {  apply Omega.HasOrdinalElem. assumption. }
    assert (:0: :< succ u) as G4. {  apply Succ.HasZero. assumption. }
    rewrite Succ.UnionOf. 2: assumption.
    split. 1: assumption. split; assumption.
  - left. destruct H2 as [H2 H3]. subst. reflexivity.
  - right. destruct H2 as [H2 [H3 H4]]. exists :U(x), y.
    assert (On x) as G5. { apply Omega.HasOrdinalElem. assumption. }
    assert (succ :U(x) = x) as H5. {
      apply Succ.OfUnion. 1: assumption.
      apply SOO.IsSuccessor; assumption. }
    rewrite H5. split. 2: assumption. reflexivity.
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

Proposition DomainOf : forall (F:Class) (a x:U), domain F :<=: toClass :N ->
  domain (shiftR a F) x <-> x = :0: \/ (:0: :< x /\ x :< :N /\ domain F :U(x)).
Proof.
  intros F a x H1. split; intros H2.
  - destruct H2 as [y H2]. apply Charac2 in H2. 2: assumption.
    destruct H2 as [[H2 H3]|[H2 [H3 H4]]].
    + left. assumption.
    + right. split. 1: assumption. split. 1: assumption. exists y. assumption.
  - destruct H2 as [H2|H2].
    + exists a. left. subst. reflexivity.
    + destruct H2 as [H2 [H3 [y H4]]]. exists y. apply Charac2. 1: assumption.
      right. split. 1: assumption. split; assumption.
Qed.

Proposition EvalZero : forall (F:Class) (a:U),
  domain F :<=: toClass :N  ->
  Functional F              ->
  (shiftR a F)!:0: = a.
Proof.
  intros F a H1 H2. apply EvalOfClass.Charac.
  - apply IsFunctional. assumption.
  - apply DomainOf. 1: assumption. left. reflexivity.
  - apply Charac2. 1: assumption. left. split; reflexivity.
Qed.

Proposition Eval : forall (F:Class) (a x:U),
  domain F :<=: toClass :N    ->
  Functional F                ->
  :0: :< x                    ->
  x :< :N                     ->
  domain F :U(x)              ->
  (shiftR a F)! x = F!:U(x).
Proof.
  intros F a x H1 H2 H3 H4 H5.
  apply EvalOfClass.Charac.
  - apply IsFunctional. assumption.
  - apply DomainOf. 1: assumption.
    right. split. 1: assumption. split; assumption.
  - apply Charac2. 1: assumption.
    right. split. 1: assumption. split. 1: assumption.
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

Proposition WhenDomainIsNat : forall (F:Class) (a n:U),
  n :< :N                                   ->
  domain F :~: toClass n                    ->
  domain (shiftR a F) :~: toClass (succ n).
Proof.
  intros F a n H1 H2 x.
  assert (On n) as G1. { apply Omega.HasOrdinalElem. assumption. }
  assert (domain F :<=: toClass :N) as G2. {
    intros m G2. apply H2 in G2. apply Omega.IsIn with n; assumption. }
  split; intros H3.
  - apply DomainOf in H3. 2: assumption.
    destruct H3 as [H3|[H3 [H4 H5]]].
    + subst. apply Succ.HasZero. assumption.
    + assert (succ :U(x) = x) as H6. { apply Omega.SuccOfUnion; assumption. }
      assert (:U(x) :< n) as H7. { apply H2. assumption. }
      assert (:U(x) :< :N) as G3. { apply Omega.IsIn with n; assumption. }
      assert (On :U(x)) as G4. { apply SOO.HasOrdinalElem. assumption. }
      rewrite <- H6. apply Succ.ElemCompat; assumption.
  - apply DomainOf. 1: assumption.
    assert (succ n :< :N) as G5. { apply Omega.HasSucc. assumption. }
    assert (x :< :N) as G6. { apply Omega.IsIn with (succ n); assumption. }
    assert (On x) as G7. { apply SOO.HasOrdinalElem. assumption. }
    assert (x = :0: \/ :0: :< x) as H4. { apply SOC.ZeroOrElem. assumption. }
    destruct H4 as [H4|H4]. 1: { left. assumption. } right.
    split. 1: assumption. split. 1: assumption. apply H2.
    assert (Ordinal :U(x)) as G8. { apply UnionOf.IsOrdinal. assumption. }
    apply Succ.ElemCompatRev; try assumption.
    rewrite Omega.SuccOfUnion; assumption.
Qed.

Proposition WhenDomainIsN : forall (F:Class) (a:U),
  domain F :~: toClass :N -> domain (shiftR a F) :~: toClass :N.
Proof.
  intros F a H1 x.
  assert (domain F :<=: toClass :N) as H2. { intros u H2. apply H1. assumption. }
  split; intros H3.
  - apply DomainOf in H3. 2: assumption. destruct H3 as [H3|[H3 [H4 H5]]]. 2: assumption.
    subst. apply Omega.HasZero.
  - apply DomainOf. 1: assumption.
    assert (On x) as G1. { apply Omega.HasOrdinalElem. assumption. }
    assert (x = :0: \/ :0: :< x) as H4. { apply SOC.ZeroOrElem. assumption. }
    destruct H4 as [H4|H4].
    + left. assumption.
    + right. split. 1: assumption. split. 1: assumption. apply H1.
      apply Omega.HasUnion. assumption.
Qed.

Proposition IsOrdFun : forall (F:Class) (a:U),
  On a                      ->
  domain F :<=: toClass :N  ->
  OrdFun F                  ->
  OrdFun (shiftR a F).
Proof.
  intros F a H1 H2 H3.
  assert (On :N) as G1. { apply Omega.IsOrdinal. }
  assert (COC.Ordinal (domain F)) as H4. { apply H3. }
  assert (domain F :~: toClass :N \/
    exists n, n :< :N /\ domain F :~: toClass n) as H5. {
      apply Omega.OrdinalSubclass; assumption. }
  split.
  - apply IsFunction, H3.
  - split.
    + destruct H5 as [H5|[n [H5 H6]]].
      * apply COC.EquivCompat with (toClass :N). 2: assumption.
        apply Equiv.Sym, WhenDomainIsN. assumption.
      * assert (On n) as G2. { apply Omega.HasOrdinalElem. assumption. }
        assert (On (succ n)) as G3. { apply Succ.IsOrdinal. assumption. }
        apply COC.EquivCompat with (toClass (succ n)). 2: assumption.
        apply Equiv.Sym, WhenDomainIsNat; assumption.
    + intros y H6. apply RangeOf in H6. destruct H6 as [H6|H6].
      * subst. assumption.
      * apply H3. assumption.
Qed.
