Require Import ZF.Axiom.Classic.
Require Import ZF.Class.Empty.
Require Import ZF.Class.Equiv.
Require Import ZF.Class.Incl.
Require Import ZF.Class.Inter2.
Require Import ZF.Class.Ordinal.Core.
Require Import ZF.Class.Ordinal.Induction2.
Require Import ZF.Class.Ordinal.OrdFun.
Require Import ZF.Class.Ordinal.Recursion2.
Require Import ZF.Class.Ordinal.Transitive.
Require Import ZF.Class.Relation.Domain.
Require Import ZF.Class.Relation.Function.
Require Import ZF.Class.Relation.Range.
Require Import ZF.Set.Core.
Require Import ZF.Set.Ordinal.Core.
Require Import ZF.Set.Ordinal.Limit.
Require Import ZF.Set.Ordinal.Natural.
Require Import ZF.Set.Ordinal.Succ.
Require Import ZF.Set.Ordinal.UnionGenOfClass.
Require Import ZF.Set.OrdPair.
Require Import ZF.Set.Relation.EvalOfClass.

Module COC := ZF.Class.Ordinal.Core.
Module CRF := ZF.Class.Relation.Function.

Module SOC := ZF.Set.Ordinal.Core.

(* A strictly monotone ordinal function.                                        *)
Definition Monotone (F:Class) : Prop := OrdFun F /\ forall (a b:U),
  domain F a -> domain F b -> a :< b -> F!a :< F!b.

Proposition IsIncl : forall (F:Class) (a:U),
  Monotone F -> domain F a -> a :<=: F!a.
Proof.
  intros F a [[H1 [H2 H3]] H4] H5.
  assert (On a) as H6. {
    apply COC.IsOrdinal with (domain F); assumption. }
  assert (On (F!a)) as H7. { apply H3, CRF.IsInRange; assumption. }
  remember (fun b => domain F b /\ F!b :< b) as A eqn:H8.
  assert (A :~: :0: \/ A :<>: :0:) as H9. { apply LawExcludedMiddle. }
  destruct H9 as [H9|H9].
  - assert (F!a :< a \/ a :<=: F!a) as H10. { apply SOC.ElemOrIncl; assumption. }
    destruct H10 as [H10|H10]. 2: assumption. exfalso.
    assert (A a) as H11. { rewrite H8. split; assumption. }
    apply H9 in H11. contradiction.
  - exfalso.
    assert (A :<=: On) as H10. {
      intros b H10. rewrite H8 in H10. apply COC.IsOrdinal with (domain F).
      1: assumption. apply H10. }
    assert (exists b, A b /\ A :/\: toClass b :~: :0:) as H11. {
      apply COC.HasEMinimal with On; try assumption. apply COC.OnIsOrdinal. }
    destruct H11 as [b [H11 H12]]. rewrite H8 in H11. destruct H11 as [H11 H13].
    assert (domain F (F!b)) as H14. {
      assert (Transitive (domain F)) as H14. { apply H2. }
      apply (H14 b); assumption. }
    assert (F!(F!b) :< F!b) as H15. { apply H4; assumption. }
    assert ((A :/\: toClass b) F!b) as H16. {
      split. 2: assumption. rewrite H8. split; assumption. }
    apply H12 in H16. contradiction.
Qed.

Lemma RecursionInitial : forall (F:Class) (a:U),
  On a                                                    ->
  a :< F!a                                                ->
  Monotone F                                              ->
  domain F :~: On                                         ->
  (forall b, On b -> b <> :0: -> a :< (Recursion F a)!b).
Proof.
  intros F a H1 H2 [H3 H4] H5.
  assert (Ordinal F!a) as H6. {
    apply H3. exists a. apply CRF.Satisfies. 1: apply H3.
    apply H5. assumption. }
  assert (range (Recursion F a) :<=: On) as H7. {
    apply OrdFun.FromRecursion; assumption. }
  remember (fun b => b <> :0: -> a :< (Recursion F a)!b) as A eqn:H8.
  assert (forall b, On b -> A b) as H9. {
    apply Induction2; rewrite H8.
    - intros H9. contradiction.
    - intros b H9 H10 _. rewrite Recursion2.WhenSucc. 2: assumption.
      assert (b = :0: \/ b <> :0:) as H11. { apply LawExcludedMiddle. }
      destruct H11 as [H11|H11].
      + subst. rewrite Recursion2.WhenZero. assumption.
      + apply SOC.ElemElemTran with F!a; try assumption.
        * apply H3. exists (Recursion F a)!b. apply CRF.Satisfies. 1: apply H3.
          apply H5, H7. exists b. apply CRF.Satisfies;
          apply Recursion2.IsFunctionOn. assumption.
        * apply H4.
          { apply H5. assumption. }
          { apply H5, H7. exists b. apply CRF.Satisfies;
            apply Recursion2.IsFunctionOn. assumption. }
          { apply H10. assumption. }
    - intros b H9 H10 _. rewrite Recursion2.WhenLimit. 2: assumption.
      apply Limit.HasOne in H9. apply UnionGenOfClass.Charac.
      exists :1:. split. 1: assumption. apply H10. 1: assumption.
      apply Empty.HasElem. exists :0:. apply Succ.IsIn. }
  rewrite H8 in H9. assumption.
Qed.

Proposition FromRecursion : forall (F:Class) (a:U),
  On a                      ->
  a :< F!a                  ->
  Monotone F                ->
  domain F :~: On           ->
  Monotone (Recursion F a).
Proof.
  intros F a H1 H2 [H3 H4] H5. split.
  - apply OrdFun.FromRecursion; assumption.
  - assert (domain (Recursion F a) :~: On) as H6. {
      apply Recursion2.IsFunctionOn. }
    intros b c H7 H8. apply H6 in H7. apply H6 in H8. revert b H7.
    remember (fun b => b :< c -> (Recursion F a)!b :< (Recursion F a)!c) as A eqn:H9.
    assert (forall b, On b -> A b) as H10. {
      apply Induction2; rewrite H9.
      - intros H10. rewrite Recursion2.WhenZero. apply RecursionInitial; try assumption.
        + split; assumption.
        + apply HasElem. exists :0:. assumption.
      - intros b H10 H11 H12. rewrite Recursion2.WhenSucc. 2: assumption.
Admitted.
