Require Import ZF.Class.Empty.
Require Import ZF.Set.Core.
Require Import ZF.Set.Empty.
Require Import ZF.Set.Foundation.
Require Import ZF.Set.Incl.
Require Import ZF.Set.Ordinal.Core.
Require Import ZF.Set.Relation.Bij.
Require Import ZF.Set.Relation.Function.
Require Import ZF.Set.Relation.Functional.
Require Import ZF.Set.Relation.Fun.
Require Import ZF.Set.Relation.Fun.IfThenElse.
Require Import ZF.Set.Relation.OneToOne.
Require Import ZF.Set.Relation.Onto.
Require Import ZF.Set.Relation.Range.
Require Import ZF.Set.Relation.Restrict.
Require Import ZF.Set.Specify.

Require Import ZF.Notation.Eval.

Module CEM := ZF.Class.Empty.
Module SOC := ZF.Set.Ordinal.Core.
Module SRB := ZF.Set.Relation.Bij.
Module SRF := ZF.Set.Relation.Fun.
Module SFI := ZF.Set.Relation.Fun.IfThenElse.
Module SRO := ZF.Set.Relation.Onto.
Module SRR := ZF.Set.Relation.Range.
Module SRS := ZF.Set.Relation.Restrict.

(* A non-empty included ordinal is the range of an ordinal retraction.          *)
Proposition WhenIncl : forall (a b:U), Ordinal a -> Ordinal b ->
  b <> :0: -> b :<=: a -> exists f, Onto f a b.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros a b H1 H2 H3 H4.
  (* Map elements of b to themselves and all remaining elements of a to 0.      *)
  remember (SFI.ifThenElse a (fun x => x :< b) (fun x => x) (fun _ => :0:))
    as f eqn:H5.
  exists f. rewrite H5. split. 1: apply SFI.IsFunctionOn.
  apply Incl.Double. split.
  - intros y H6. apply SRR.Charac in H6. destruct H6 as [x H6].
    apply SFI.Charac2 in H6. destruct H6 as [[H6 [_ H7]]|[H6 [_ _]]].
    + rewrite H6. assumption.
    + rewrite H6. apply SOC.HasZero; assumption.
  - intros y H6. apply SRR.Charac. exists y.
    apply (SFI.Satisfies1 (fun x => x :< b) (fun x => x) (fun _ => :0:) a y).
    + apply H4. assumption.
    + assumption.
Qed.

(* A surjection from an ordinal has a restriction which is a bijection.         *)
Proposition HasRestrictBij : forall (f a b:U), Ordinal a ->
  Onto f a b -> exists c, c :<=: a /\ Bij (f:|:c) c b.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros f a b H1 H2.
  (* Keep the first point of each fiber of f, in the ordinal order of a.        *)
  remember {{ x :< a | fun x => forall y, y :< x -> f!y <> f!x }} as c eqn:H3.
  assert (c :<=: a) as H4. { rewrite H3. apply Specify.IsInclL. }
  assert (SRF.Fun f a b) as H5. { apply SRO.IsFun. assumption. }
  assert (Function f) as G1. { apply H5. }
  assert (Functional f) as G2. { apply G1. }
  assert (SRF.Fun (f:|:c) c b) as H6. {
    apply SRF.Restrict with a; assumption. }
  assert (OneToOne (f:|:c)) as H7. {
    apply SRF.IsOneToOne with c b. 1: assumption.
    intros x y H7 H8 H9.
    rewrite (SRS.Eval f c x) in H9; try assumption.
    rewrite (SRS.Eval f c y) in H9; try assumption.
    assert (x :< a) as H10. { apply H4. assumption. }
    assert (y :< a) as H11. { apply H4. assumption. }
    assert (Ordinal x) as H12. { apply SOC.IsOrdinal with a; assumption. }
    assert (Ordinal y) as H13. { apply SOC.IsOrdinal with a; assumption. }
    assert (x = y \/ x :< y \/ y :< x) as H14. {
      apply SOC.IsTotal; assumption. }
    destruct H14 as [H14|[H14|H14]]. 1: assumption.
    - exfalso. rewrite H3 in H8. apply Specify.Charac in H8.
      destruct H8 as [_ H8]. apply H8 with x; assumption.
    - exfalso. rewrite H3 in H7. apply Specify.Charac in H7.
      destruct H7 as [_ H7]. apply H7 with y. 1: assumption.
      symmetry. assumption. }
  assert (b :<=: SRR.range (f:|:c)) as H8. {
    intros z H8.
    assert (exists x, x :< a /\ f!x = z) as H9. {
      apply (SRO.RangeCharac f a b z) in H8. 2: assumption.
      assumption. }
    destruct H9 as [x [H9 H10]].
    remember (fun y => y :< a /\ f!y = z) as A eqn:H11.
    assert (exists n, Ordinal n /\ A n /\ forall y, A y -> n :<=: y) as H12. {
      apply SOC.HasMinimal.
      - rewrite H11. intros y H12. destruct H12 as [H12 _].
        apply SOC.IsOrdinal with a; assumption.
      - apply CEM.HasElem. exists x. rewrite H11. split; assumption. }
    destruct H12 as [n [H12 [H13 H14]]]. rewrite H11 in H13.
    destruct H13 as [H13 H15].
    assert (n :< c) as H16. {
      rewrite H3. apply Specify.Charac. split. 1: assumption.
      intros y H16 H17.
      assert (y :< a) as H18. {
        assert (n :<=: a) as H18. { apply SOC.ElemIsIncl; assumption. }
        apply H18. assumption. }
      assert (A y) as H19. { rewrite H11. split. 1: assumption.
        rewrite H17. assumption. }
      assert (n :<=: y) as H20. { apply H14. assumption. }
      assert (y :< y) as H21. { apply H20. assumption. }
      revert H21. apply Foundation.NoLoop1. }
    apply SRR.Charac. exists n. apply SRS.Charac2. split. 1: assumption.
    rewrite <- H15. apply SRO.Satisfies with a b; assumption. }
  exists c. split. 1: assumption. apply SRB.FromFun; assumption.
Qed.
