Require Import ZF.Class.Equiv.
Require Import ZF.Class.Ordinal.ShiftR.
Require Import ZF.Class.Small.
Require Import ZF.Set.Core.
Require Import ZF.Set.Incl.
Require Import ZF.Set.Empty.
Require Import ZF.Set.FromClass.
Require Import ZF.Set.Ordinal.Core.
Require Import ZF.Set.Ordinal.Decreasing.
Require Import ZF.Set.Ordinal.Omega.
Require Import ZF.Set.Ordinal.OrdFun.
Require Import ZF.Set.Ordinal.OrdFunOn.
Require Import ZF.Set.Ordinal.Succ.
Require Import ZF.Set.Ordinal.UnionOf.
Require Import ZF.Set.OrdPair.
Require Import ZF.Set.Relation.Domain.
Require Import ZF.Set.Relation.Eval.
Require Import ZF.Set.Relation.Function.
Require Import ZF.Set.Relation.Functional.
Require Import ZF.Set.Relation.Range.
Require Import ZF.Set.Relation.Relation.
Require Import ZF.Set.Single.
Require Import ZF.Set.Union.
Require Import ZF.Set.Union2.

Require Import ZF.Notation.Eval.

Module COS := ZF.Class.Ordinal.ShiftR.

(* Shifting a function to the right. shiftR a f = {(0,a)}\/{(succ x,y)|(x,y):<f}*)
Definition shiftR (a f:U) : U := fromClass (COS.shiftR a (toClass f))
  (COS.IsSmall (toClass f) a (SetIsSmall f)).

Proposition ToClass : forall (f a:U),
  toClass (shiftR a f) :~: COS.shiftR a (toClass f).
Proof.
  intros f a. apply ToFromClass.
Qed.

Proposition Charac : forall (f a x:U),
  x :< shiftR a f <->
  x = :(:0:,a): \/ exists y z, x = :(succ y,z): /\ :(y,z): :< f.
Proof.
  intros f a x. split; intros H1.
  - apply FromClass.Charac in H1. destruct H1 as [H1|H1].
    + left. assumption.
    + right. assumption.
  - apply FromClass.Charac. destruct H1 as [H1|H1].
    + left. assumption.
    + right. assumption.
Qed.

Proposition Charac2 : forall (f a x y:U), domain f :<=: :N ->
  :(x,y): :< shiftR a f <->
  x = :0: /\ y = a \/ :0: :< x /\ x :< :N /\ :(:U(x),y): :< f.
Proof.
  intros f a x y H1. split; intros H2.
  - apply Charac in H2. destruct H2 as [H2|H2].
    + left. apply OrdPair.WhenEqual in H2. assumption.
    + right. destruct H2 as [u [v [H2 H3]]].
      apply OrdPair.WhenEqual in H2. destruct H2 as [H2 H4]. subst.
      assert (u :< :N) as G1. { apply H1, Domain.Charac. exists v. assumption. }
      assert (succ u :< :N) as G2. { apply Omega.HasSucc. assumption. }
      assert (Ordinal u) as G3. {  apply Omega.HasOrdinalElem. assumption. }
      assert (:0: :< succ u) as G4. {  apply Succ.HasZero. assumption. }
      rewrite Succ.UnionOf. 2: assumption.
      split. 1: assumption. split; assumption.
  - destruct H2 as [H2|H2]; apply Charac.
    + left. destruct H2 as [H2 H3]. subst. reflexivity.
    + right. destruct H2 as [H2 [H3 H4]]. exists :U(x), y.
      assert (Ordinal x) as G5. { apply Omega.HasOrdinalElem. assumption. }
      assert (succ :U(x) = x) as H5. {
        apply Succ.OfUnion. 1: assumption.
        apply SOO.IsSuccessor; assumption. }
      rewrite H5. split. 2: assumption. reflexivity.
Qed.

Proposition IsRelation : forall (f a:U), Relation (shiftR a f).
Proof.
  intros f a x H1. apply Charac in H1. destruct H1 as [H1|H1].
  - exists :0:, a. assumption.
  - destruct H1 as [y [z [H1 _]]]. exists (succ y), z. assumption.
Qed.

Proposition IsFunctional : forall (f a:U), domain f :<=: :N ->
  Functional f -> Functional (shiftR a f).
Proof.
  intros f a G1 H1 y z1 z2 H2 H3.
  apply Charac2 in H2. 2: assumption.
  apply Charac2 in H3. 2: assumption.
  destruct H2 as [H2|H2]; destruct H3 as [H3|H3].
  - destruct H2 as [H2 H4]. destruct H3 as [H3 H5]. subst. reflexivity.
  - exfalso. destruct H2 as [H2 H4]. destruct H3 as [H3 [H5 H6]]. subst.
    apply Empty.Charac in H3. contradiction.
  - exfalso. destruct H3 as [H3 H4]. destruct H2 as [H2 [H5 H6]]. subst.
    apply Empty.Charac in H2. contradiction.
  - destruct H2 as [H2 [H4 H5]]. destruct H3 as [H3 [H6 H7]].
    apply H1 with :U(y); assumption.
Qed.

Proposition IsFunction : forall (f a:U), domain f :<=: :N ->
  Functional f -> Function (shiftR a f).
Proof.
  intros f a H1 H2. split.
  - apply IsRelation.
  - apply IsFunctional; assumption.
Qed.

Proposition DomainOf : forall (f a x:U), domain f :<=: :N ->
  x :< domain (shiftR a f) <->
  x = :0: \/ (:0: :< x /\ x :< :N /\ :U(x) :< domain f).
Proof.
  intros f a x H1. split; intros H2.
  - apply Domain.Charac in H2. destruct H2 as [y H2].
    apply Charac2 in H2. 2: assumption.
    destruct H2 as [[H2 H3]|[H2 [H3 H4]]].
    + left. assumption.
    + right. split. 1: assumption. split. 1: assumption.
      apply Domain.Charac. exists y. assumption.
  - destruct H2 as [H2|H2]; apply Domain.Charac.
    + exists a. apply Charac2. 1: assumption. left. subst. split; reflexivity.
    + destruct H2 as [H2 [H3 H4]].
      apply Domain.Charac in H4. destruct H4 as [y H4]. exists y.
      apply Charac2. 1: assumption. right. split. 1: assumption.
      split; assumption.
Qed.

Proposition EvalZero : forall (f a:U), domain f :<=: :N ->
  Functional f -> (shiftR a f)!:0: = a.
Proof.
  intros f a H1 H2. apply Eval.Charac.
  - apply IsFunctional; assumption.
  - apply DomainOf. 1: assumption. left. reflexivity.
  - apply Charac2. 1: assumption. left. split; reflexivity.
Qed.

Proposition Eval : forall (f a n:U),
  domain f :<=: :N            ->
  Functional f                ->
  :0: :< n                    ->
  n :< :N                     ->
  :U(n) :< domain f           ->
  (shiftR a f)!n = f!:U(n).
Proof.
  intros f a n H1 H2 H3 H4 H5. apply Eval.Charac.
  - apply IsFunctional; assumption.
  - apply DomainOf. 1: assumption. right.
    split. 1: assumption. split; assumption.
  - apply Charac2. 1: assumption. right.
    split. 1: assumption. split. 1: assumption.
    apply Eval.Satisfies; assumption.
Qed.

Proposition EvalSucc : forall (f a n:U),
  domain f :<=: :N            ->
  Functional f                ->
  n :< :N                     ->
  n :< domain f               ->
  (shiftR a f)!(succ n) = f!n.
Proof.
  intros f a n H1 H2 H3 H4.
  assert (succ n :< :N) as G1. { apply Omega.HasSucc. assumption. }
  assert (:U(succ n) = n) as G2. { apply Omega.UnionOfSucc. assumption. }
  assert (Ordinal n) as G3. { apply Omega.HasOrdinalElem. assumption. }
  rewrite Eval, G2; try assumption. 1: reflexivity.
  - apply Succ.HasZero. assumption.
  - rewrite G2. assumption.
Qed.

Proposition RangeOf : forall (f a:U), domain f :<=: :N ->
  range (shiftR a f) = :{a}: :\/: range f.
Proof.
  intros f a H1. apply DoubleInclusion. split; intros y H2.
  - apply Range.Charac in H2. destruct H2 as [x H2].
    apply Charac2 in H2. 2: assumption.
    destruct H2 as [[H2 H3]|[H2 [H3 H4]]]; apply Union2.Charac.
    + left. apply Single.Charac. assumption.
    + right. apply Range.Charac. exists :U(x). assumption.
  - apply Union2.Charac in H2. destruct H2 as [H2|H2]; apply Range.Charac.
    + apply Single.Charac in H2. subst. exists :0:.
      apply Charac2. 1: assumption. left. split; reflexivity.
    + apply Range.Charac in H2. destruct H2 as [x H2].
      exists (succ x). apply Charac2. 1: assumption. right.
      assert (x :< domain f) as G1. {
        apply Domain.Charac. exists y. assumption. }
      assert (x :< :N) as G2. { apply H1. assumption. }
      assert (Ordinal x) as G3. { apply Omega.HasOrdinalElem. assumption. }
      assert ((succ x) :< :N) as G4. { apply Omega.HasSucc. assumption. }
      assert (:U(succ x) = x) as H3. { apply Omega.UnionOfSucc. assumption. }
      rewrite H3. split.
      * apply Succ.HasZero. assumption.
      * split; assumption.
Qed.

Proposition WhenDomainIsNat : forall (f a:U),
  domain f :< :N -> domain (shiftR a f) = succ (domain f).
Proof.
  intros f a H1. remember (domain f) as n eqn:H2. symmetry in H2.
  assert (domain f :<=: :N) as G1. {
    intros m G1. apply Omega.IsIn with n. 2: assumption.
    subst. assumption. }
  assert (Ordinal n) as G2. { apply Omega.HasOrdinalElem. assumption. }
  apply DoubleInclusion. split; intros x H3.
  - apply DomainOf in H3. 2: assumption. destruct H3 as [H3|[H3 [H4 H5]]].
    + rewrite H3. apply Succ.HasZero. assumption.
    + assert (succ :U(x) = x) as H6. { apply Omega.SuccOfUnion; assumption. }
      assert (:U(x) :< n) as H7. { rewrite <- H2. assumption. }
      assert (:U(x) :< :N) as G3. { apply Omega.IsIn with n; assumption. }
      assert (Ordinal :U(x)) as G4. { apply Omega.HasOrdinalElem. assumption. }
      rewrite <- H6. apply Succ.ElemCompat; assumption.
  - apply DomainOf. 1: assumption.
    assert (succ n :< :N) as G5. { apply Omega.HasSucc. assumption. }
    assert (x :< :N) as G6. { apply Omega.IsIn with (succ n); assumption. }
    assert (Ordinal x) as G7. { apply Omega.HasOrdinalElem. assumption. }
    assert (x = :0: \/ :0: :< x) as H4. { apply SOC.ZeroOrElem. assumption. }
    destruct H4 as [H4|H4]. 1: { left. assumption. } right.
    split. 1: assumption. split. 1: assumption. rewrite H2.
    assert (Ordinal :U(x)) as G8. { apply UnionOf.IsOrdinal. assumption. }
    apply Succ.ElemCompatRev; try assumption.
    rewrite Omega.SuccOfUnion; assumption.
Qed.

Proposition WhenDomainIsN : forall (f a:U),
  domain f = :N -> domain (shiftR a f) = :N.
Proof.
  intros f a H1.
  assert (domain f :<=: :N) as H2. { rewrite H1. apply Incl.Refl. }
  apply DoubleInclusion. split; intros x H3.
  - apply DomainOf in H3. 2: assumption.
    destruct H3 as [H3|[H3 [H4 H5]]]. 2: assumption. subst. apply Omega.HasZero.
  - apply DomainOf. 1: assumption.
    assert (Ordinal x) as G1. { apply Omega.HasOrdinalElem. assumption. }
    assert (x = :0: \/ :0: :< x) as H4. { apply SOC.ZeroOrElem. assumption. }
    destruct H4 as [H4|H4].
    + left. assumption.
    + right. split. 1: assumption. split. 1: assumption. rewrite H1.
      apply Omega.HasUnion. assumption.
Qed.

Proposition IsOrdFun : forall (f a:U),
  Ordinal a             ->
  domain f :<=: :N      ->
  OrdFun f              ->
  OrdFun (shiftR a f).
Proof.
  intros f a H1 H2 H3.
  assert (Ordinal (domain f)) as G1. { destruct H3 as [_ [H3 _]]. assumption. }
  assert (Ordinal :N) as G2. { apply Omega.IsOrdinal. }
  assert (Ordinal (succ (domain f))) as G3. {
    apply Succ.IsOrdinal. assumption. }
  assert (domain f = :N \/ domain f :< :N) as H5. {
    apply Core.EqualOrElem; assumption. }
  split.
  - apply IsFunction. 1: assumption. apply H3.
  - split.
    + destruct H5 as [H5|H5].
      * rewrite WhenDomainIsN; assumption.
      * rewrite WhenDomainIsNat; assumption.
    + intros y H6. rewrite RangeOf in H6. 2: assumption.
      apply Union2.Charac in H6. destruct H6 as [H6|H6].
      * apply Single.Charac in H6. subst. assumption.
      * apply H3. assumption.
Qed.

Proposition IsOrdFunOnNat : forall (f a n:U),
  Ordinal a                       ->
  n :< :N                         ->
  OrdFunOn f n                    ->
  OrdFunOn (shiftR a f) (succ n).
Proof.
  intros f a n H1 H2 [H3 H4].
  assert (Ordinal :N) as G1. { apply Omega.IsOrdinal. }
  split.
  - apply IsOrdFun; try assumption. rewrite H4.
    apply Core.ElemIsIncl; assumption.
  - rewrite WhenDomainIsNat; rewrite H4. 2: assumption. reflexivity.
Qed.

Proposition IsOrdFunOnN : forall (f a:U),
  Ordinal a                 ->
  OrdFunOn f :N             ->
  OrdFunOn (shiftR a f) :N.
Proof.
  intros f a H1 [H2 H3].
  split.
  - apply IsOrdFun; try assumption. rewrite H3. apply Incl.Refl.
  - rewrite WhenDomainIsN. 2: assumption. reflexivity.
Qed.

Proposition IsDecreasing : forall (f a:U),
  OrdFun f                                ->
  domain f :< :N                          ->
  Ordinal a                               ->
  (forall i, i :< domain f -> f!i :< a)   ->
  Decreasing f                            ->
  Decreasing (shiftR a f).
Proof.
  intros f a [H1 [H2 H3]] H4 H5 H6 H7 x y H8 H9 H10.
  assert (Ordinal :N) as G1. { apply Omega.IsOrdinal. }
  assert (domain f :<=: :N) as G2. { apply Core.ElemIsIncl; assumption. }
  rewrite WhenDomainIsNat in H8. 2: assumption.
  rewrite WhenDomainIsNat in H9. 2: assumption.
  remember (domain f) as n eqn:H11. symmetry in H11.
  assert (Ordinal n) as G3. { apply Omega.HasOrdinalElem. assumption. }
  assert (succ n :< :N) as G4. { apply Omega.HasSucc. assumption. }
  assert (Ordinal (succ n)) as G5. { apply Omega.HasOrdinalElem. assumption. }
  assert (x :< :N) as G6. { apply Omega.IsIn with (succ n); assumption. }
  assert (y :< :N) as G7. { apply Omega.IsIn with (succ n); assumption. }
  assert (Ordinal x) as G8. { apply Omega.HasOrdinalElem. assumption. }
  assert (Ordinal y) as G9. { apply Omega.HasOrdinalElem. assumption. }
  assert (Functional f) as G10. { apply H1. }
  assert (domain f :<=: :N) as G11. { rewrite H11. assumption. }
  assert (x = :0: \/ :0: :< x) as H12. { apply Core.ZeroOrElem. assumption. }
  assert (y = :0: \/ :0: :< y) as H13. { apply Core.ZeroOrElem. assumption. }
  assert (forall i, i :< succ n -> :0: :< i -> :U(i) :< domain f) as H14. {
    intros i H14 H15. rewrite H11.
    assert (i :< :N) as G12. { apply Omega.IsIn with (succ n); assumption. }
    assert (Ordinal i) as G13. { apply Omega.HasOrdinalElem. assumption. }
    assert (Ordinal :U(i)) as G14. { apply UnionOf.IsOrdinal. assumption. }
    apply Succ.ElemCompatRev; try assumption.
    rewrite Omega.SuccOfUnion; assumption. }
  destruct H12 as [H12|H12]; destruct H13 as [H13|H13].
  - exfalso. subst. apply Empty.Charac in H10. contradiction.
  - assert (:U(y) :< domain f) as H15. { apply H14; assumption. }
    rewrite H12, EvalZero, Eval; try assumption.
    assert (Ordinal :U(y)) as G15. {
      apply Core.IsOrdinal with (domain f). 2: assumption.
      rewrite H11. assumption. }
    apply H6. rewrite <- H11. assumption.
  - exfalso. rewrite H13 in H10. apply Empty.Charac in H10. contradiction.
  - assert (:U(x) :< domain f) as H15. { apply H14; assumption. }
    assert (:U(y) :< domain f) as H16. { apply H14; assumption. }
    rewrite Eval, Eval; try assumption.
    assert (Ordinal :U(x)) as G15. {
      apply Core.IsOrdinal with (domain f). 2: assumption.
      rewrite H11. assumption. }
    assert (Ordinal :U(y)) as G16. {
      apply Core.IsOrdinal with (domain f). 2: assumption.
      rewrite H11. assumption. }
    apply H7; try assumption.
    apply Succ.ElemCompatRev; try assumption.
    rewrite Omega.SuccOfUnion, Omega.SuccOfUnion; assumption.
Qed.

