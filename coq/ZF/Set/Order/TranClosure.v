Require Import ZF.Class.Incl.
Require Import ZF.Class.Equiv.
Require Import ZF.Class.Order.Founded2.
Require Import ZF.Class.Order.TranClosure.
Require Import ZF.Class.Order.WellFounded.
Require Import ZF.Set.Core.
Require Import ZF.Set.Empty.
Require Import ZF.Set.FromClass.
Require Import ZF.Set.Incl.
Require Import ZF.Set.Order.InitSegment.
Require Import ZF.Set.Ordinal.Natural.
Require Import ZF.Set.Ordinal.Omega.
Require Import ZF.Set.Ordinal.Succ.
Require Import ZF.Set.OrdPair.
Require Import ZF.Set.Relation.Domain.
Require Import ZF.Set.Relation.Eval.
Require Import ZF.Set.Relation.Fun.
Require Import ZF.Set.Relation.Functional.
Require Import ZF.Set.Relation.FunctionOn.
Require Import ZF.Set.Relation.Range.
Require Import ZF.Set.Relation.ShiftR.
Require Import ZF.Set.Single.
Require Import ZF.Set.Union2.

Require Import ZF.Notation.Eval.

Module CIN := ZF.Class.Incl.
Module COT := ZF.Class.Order.TranClosure.

(* An R-transitive set a in class A,                                            *)
Definition Transitive (R A:Class) (a:U) : Prop := COT.Transitive R A a.

(* The R-transitive closure of a in A.                                          *)
Definition closure (R A:Class) (a:U) : U :=
  fromClass (COT.closure R A a) (COT.IsSmall R A a).

Lemma IsClosure : forall (R A:Class) (a:U),
  WellFounded R A                       ->
  toClass a :<=: A                      ->
  COT.IsClosure R A a (closure R A a).
Proof.
  intros R A a H1 H2.
  assert (exists b, IsClosure R A a b) as H3. { apply COT.Exists; assumption. }
  destruct H3 as [b H3].
  assert (b = closure R A a) as H4. {
    apply DoubleInclusion. split; intros x H4.
    - apply FromClass.Charac. exists b. split; assumption.
    - apply FromClass.Charac in H4. destruct H4 as [c [H4 H5]].
      assert (b = c) as H6. { apply COT.IsUnique with R A a; assumption. }
      subst. assumption. }
  subst. assumption.
Qed.

(* The R-transitive closure of a in A contains (all elemnts of) a.              *)
Proposition Contains : forall (R A:Class) (a:U),
  WellFounded R A                       ->
  toClass a :<=: A                      ->
  a :<=: closure R A a.
Proof.
  intros R A a H1 H2. apply COT.Contains with R A, IsClosure; assumption.
Qed.

(* The R-transitive closure of a in A is a subset of A.                         *)
Proposition IsIncl : forall (R A:Class) (a:U),
  WellFounded R A                       ->
  toClass a :<=: A                      ->
  toClass (closure R A a) :<=: A.
Proof.
  intros R A a H1 H2. apply COT.IsIncl with R a, IsClosure; assumption.
Qed.

(* The R-transitive closure of a in A is R-transitive in A..                    *)
Proposition IsTransitive : forall (R A:Class) (a:U),
  WellFounded R A                       ->
  toClass a :<=: A                      ->
  Transitive R A (closure R A a).
Proof.
  intros R A a H1 H2. apply COT.IsTransitive with a, IsClosure; assumption.
Qed.

Proposition DecreasingPath : forall (R A:Class) (a x:U),
  WellFounded R A                               ->
  toClass a :<=: A                              ->
  x :< closure R A a                            ->
  exists n f,
    n :< :N                                     /\
    Fun f (succ n) (closure R A a)              /\
    f!:0: :< a                                  /\
    f!n = x                                     /\
    (forall i, i :< n -> R :(f!(succ i),f!i):).
Proof.
  intros R A a x H1 H2 H3.
  apply COT.DecreasingPath with A. 2: assumption.
  apply IsClosure; assumption.
Qed.

(* The R-transitive closure in A is the smallest R-transitive set such that ... *)
Proposition IsSmallest : forall (R A:Class) (a b:U),
  WellFounded R A       ->
  toClass a :<=: A      ->
  a :<=: b              ->
  toClass b :<=: A      ->
  Transitive R A b      ->
  closure R A a :<=: b.
Proof.
  intros R A a b H1 H2. apply COT.IsSmallest, IsClosure; assumption.
Qed.

(* a is R-transitive in A iff the initial segments of all elements are subsets. *)
Proposition InitSegment : forall (R A:Class) (a:U),
  WellFounded R A                                  ->
  toClass a :<=: A                                 ->
  Transitive R A a                                <->
  (forall x, x :< a -> initSegment R A x :<=: a).
Proof.
  intros R A a H1 H2.
  assert (A :<=: A) as G1. { apply CIN.Refl. }
  split; intros H3.
  - intros x H4 y H5.
    apply (InitSegment.Charac R A A) in H5; try assumption.
    destruct H5 as [H5 H6].
    + revert H5 H6 H4. apply H3.
    + apply H2. assumption.
  - intros x y H4 H5 H6. apply (H3 y). 1: assumption.
    apply InitSegment.CharacRev with A; try assumption.
    apply H2. assumption.
Qed.

(* A set does not belong to the R-transitive of its initial segment in A.       *)
Proposition IsNotIn : forall (R A:Class) (a:U),
  WellFounded R A                         ->
  A a                                     ->
  ~ a :< closure R A (initSegment R A a).
Proof.
  intros R A a H1 H2 H3.
  assert (A :<=: A) as G1. { apply CIN.Refl. }
  remember (closure R A (initSegment R A a)) as b eqn:H4.
  assert (exists n f,
    n :< :N                                     /\
    Fun f (succ n) b                            /\
    f!:0: :< initSegment R A a                  /\
    f!n = a                                     /\
    (forall i, i :< n -> R :(f!(succ i),f!i):)) as H5. {
      rewrite H4. apply DecreasingPath. 1: assumption.
      - apply (InitSegment.IsIncl R A A); assumption.
      - rewrite <- H4. assumption. }
  destruct H5 as [n [f [H5 [H6 [H7 [H8 H9]]]]]].
  remember (ShiftR.shiftR a f) as g eqn:H10.
  assert (domain f = succ n) as G2. { apply H6. }
  apply (Founded2.NoLoopDec R A). 1: apply H1. exists (succ n), g.
  assert (succ n :< :N) as H11. { apply Omega.HasSucc. assumption. }
  assert (:1: :<=: succ n) as H12. { apply Omega.OneInclSucc. assumption. }
  assert (FunctionOn g (succ (succ n))) as H13. {
    rewrite H10. apply ShiftR.IsFunctionOn. 1: assumption. apply H6. }
  assert (g!:0: = a) as H14. {
    rewrite H10. apply ShiftR.EvalZero.
    - rewrite G2. apply Omega.IsIncl. assumption.
    - apply H6. }
  assert (g!(succ n) = a) as H15. {
    rewrite H10. rewrite ShiftR.EvalSucc; try assumption.
    - rewrite G2. apply Omega.IsIncl. assumption.
    - apply H6.
    - rewrite G2. apply Succ.IsIn. }
  assert (g!:0: = g!(succ n)) as H16. { rewrite H14, H15. reflexivity. }
  assert (toClass (initSegment R A a) :<=: A) as H17. {
    apply InitSegment.IsIncl with A; assumption. }
  assert (toClass b :<=: A) as H18. { rewrite H4. apply IsIncl; assumption. }
  assert (range g = :{a}: :\/: range f) as H19. {
    rewrite H10. apply ShiftR.RangeOf. rewrite G2.
    apply Omega.IsIncl. assumption. }
  assert (range f :<=: b) as H20. { apply H6. }
  assert (toClass (range g) :<=: A) as H21. {
    intros y H21. rewrite H19 in H21. apply Union2.Charac in H21.
    destruct H21 as [H21|H21].
    - apply Single.Charac in H21. subst. assumption.
    - apply H18, H20. assumption. }
  assert (forall i, i :< succ (succ n) -> g!i :< range g) as H22. {
    intros i H22. apply Range.Charac. exists i.
    apply FunctionOn.Satisfies with (succ (succ n)); assumption. }
  assert (forall i, i :< succ (succ n) -> A g!i) as H23. {
    intros i H23. apply H21, H22. assumption. }
  assert (forall i, i :< succ n -> R :(g!(succ i),g!i):) as H24. {
    intros i H24.
    assert (i :< :N) as K1. { apply (Omega.IsIncl (succ n)); assumption. }
    assert (i = :0: \/ :0: :< i) as H25. { apply Omega.ZeroOrElem. assumption. }
    assert (domain f :<=: :N) as K2. {
      rewrite G2. apply Omega.IsIncl. assumption. }
    assert (Functional f) as K3. { apply H6. }
    destruct H25 as [H25|H25].
    - rewrite H25, H14, H10, ShiftR.EvalSucc; try assumption.
      + apply (InitSegment.IsLess R A A); assumption.
      + apply Omega.HasZero.
      + rewrite G2. apply Omega.SuccHasZero. assumption.
    - apply Omega.IsSuccessor in H25. 2: assumption.
      destruct H25 as [H25 [j H26]].
      assert (j :< :N) as K4. {
        apply Omega.HasSuccRev. rewrite <- H26. assumption. }
      assert (succ j :< :N) as K5. { apply Omega.HasSucc. assumption. }
      assert (j :< domain f) as K6. {
        rewrite G2. apply Omega.SuccElemCompatRev; try assumption.
        rewrite <- H26. apply (Succ.IsIncl (succ n)). assumption. }
      assert (succ j :< domain f) as K7. {
        rewrite G2. rewrite <- H26. assumption. }
      rewrite H26, H10, ShiftR.EvalSucc, ShiftR.EvalSucc; try assumption.
      apply H9. apply Omega.SuccElemCompatRev; try assumption.
      rewrite <- H26. assumption. }
  split. 1: assumption. split. 1: assumption. split. 1: assumption.
  split. 1: assumption. split; assumption.
Qed.

