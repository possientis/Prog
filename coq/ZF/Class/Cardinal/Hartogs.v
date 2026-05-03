Require Import ZF.Axiom.Classic.
Require Import ZF.Class.Cardinal.Isom.
Require Import ZF.Class.Equiv.
Require Import ZF.Class.Small.
Require Import ZF.Set.Core.
Require Import ZF.Set.Empty.
Require Import ZF.Set.Incl.
Require Import ZF.Set.Order.Isom.
Require Import ZF.Set.Order.Transport.
Require Import ZF.Set.Order.WellOrdering.
Require Import ZF.Set.Ordinal.Core.
Require Import ZF.Set.Ordinal.Order.E.
Require Import ZF.Set.OrdPair.
Require Import ZF.Set.Power.
Require Import ZF.Set.Prod.
Require Import ZF.Set.Relation.Bij.
Require Import ZF.Set.Relation.BijectionOn.
Require Import ZF.Set.Relation.Converse.
Require Import ZF.Set.Relation.Domain.
Require Import ZF.Set.Relation.Eval.
Require Import ZF.Set.Relation.FunctionOn.
Require Import ZF.Set.Relation.Image.
Require Import ZF.Set.Relation.Inj.
Require Import ZF.Set.Relation.EvalOfClass.
Require Import ZF.Set.Relation.Fun.IfThenElse2.
Require Import ZF.Set.Relation.Range.
Require Import ZF.Set.Specify.

Require Import ZF.Notation.Eval.
Require Import ZF.Notation.Image.

Module CCI := ZF.Class.Cardinal.Isom.


Definition hartogs (a:U) : Class := fun b =>
  Ordinal b /\ exists f, Inj f b a.

Proposition IsSmall : forall (a:U), Small (hartogs a).
Proof.
  intros a.
  remember (fun y => exists r x, y = :(r,x): /\ WellOrdering r x) as WO eqn:H1.
  assert (forall r x, WO :(r,x): <-> WellOrdering r x) as H2. {
    intros r x. split; intros H2.
    - rewrite H1 in H2. destruct H2 as [r' [x' [H2 H3]]].
      apply OrdPair.WhenEqual in H2. destruct H2 as [H2 H4]. subst. assumption.
    - rewrite H1. exists r, x. split. 2: assumption. reflexivity. }
  remember (ifThenElse2 :P(a :x: a) :P(a) WO
      (fun r x => (CCI.isom!:(r,x):) :[x]:) (fun _ _ => :0:)) as f eqn:H3.
  assert (forall y, y :< range f <-> hartogs a y) as H4. {
    intros y. split; intros H4.
    - apply (FunctionOn.RangeCharac f (:P(a :x: a) :x: :P(a))) in H4.
      2: { rewrite H3. apply IfThenElse2.IsFunctionOn. }
      destruct H4 as [u [H4 H5]]. apply Prod.Charac in H4.
      destruct H4 as [r [x [H4 [H6 H7]]]]. rewrite H4 in H5. clear H4.
      assert (WO :(r,x): \/ ~ WO :(r,x):) as [H8|H8]. { apply LawExcludedMiddle. }
      + assert ((f!:(r,x):) = (CCI.isom!:(r,x):) :[x]:) as H9. {
          rewrite H3. rewrite IfThenElse2.Eval1 by assumption. reflexivity. }
        unfold hartogs.
        assert (Ordinal y) as H10. {
          rewrite <- H5, H9. apply Isom.IsOrdinal, H2. assumption. }
        remember (CCI.isom!:(r,x):) as g eqn:H11.
        assert (Isom g r (E y) x y) as H12. {
          rewrite H11. apply Isom.IsIsom. 1: apply H2; assumption.
          rewrite H5, H11 in H9. assumption. }
        assert (Bij g^:-1: y x) as H13. { apply Bij.Converse, H12. }
        assert (Inj g^:-1: y a) as H14. {
          split. 1: apply H13.
          assert (range g^:-1: = x) as Hrange. { apply H13. }
          rewrite Hrange. apply Power.Charac. assumption. }
        split. 1: assumption. exists g^:-1:. assumption.
      + assert ((f!:(r,x):) = :0:) as H9. {
          rewrite H3. rewrite IfThenElse2.Eval2 by assumption. reflexivity. }
        assert (y = :0:) as H10. { rewrite <- H5, H9. reflexivity. }
        unfold hartogs. rewrite H10. split. 1: apply Core.ZeroIsOrdinal.
        exists :0:. apply Inj.WhenEmpty. reflexivity.
    - destruct H4 as [H4 [i H5]].
      remember (range i) as x eqn:H6.
      assert (x :<=: a) as H7. { rewrite H6. apply H5. }
      assert (Bij i y x) as H8. {
        split.
        - apply H5.
        - symmetry. assumption. }
      remember (transport i (E y) y) as r eqn:H9.
      assert (Isom i (E y) r y x) as H10. { apply Isom.Transport; assumption. }
      assert (WellOrdering (E y) y) as H11. {
        apply E.IsWellOrdering. assumption. }
      assert (WellOrdering r x) as H12. {
        apply WellOrdering.Transport with i (E y) y; assumption. }
      assert (WO :(r,x):) as H13. { apply H2. assumption. }
      assert (Isom i^:-1: r (E y) x y) as H14. { apply Isom.Converse. assumption. }
      assert ((CCI.isom!:(r,x):) = i^:-1:) as H15. {
        apply CCI.Eval with y; assumption. }
      assert (i^:-1: :[x]: = y) as H16. { apply Bij.ImageOfDomain, H14. }
      assert (x :< :P(a)) as H17. { apply Power.Charac. assumption. }
      assert (domain i = y) as H18. { apply H8. }
      assert (r :<=: i:[y]: :x: i:[y]:) as H19. {
        rewrite H9. apply Transport.IsIncl.
        - apply H8.
        - rewrite H18. apply Incl.Refl. }
      assert (i:[y]: = x) as H20. { apply Bij.ImageOfDomain. assumption. }
      assert (r :< :P(a :x: a)) as H21. {
        apply Power.Charac. intros z H21. apply H19 in H21.
        rewrite H20 in H21. apply Prod.Charac in H21.
        destruct H21 as [u [v [H21 [H22 H23]]]].
        apply Prod.Charac. exists u, v. split. 1: assumption.
        split; apply H7; assumption. }
      assert ((f!:(r,x):) = (CCI.isom!:(r,x):) :[x]:) as H22. {
        rewrite H3. rewrite IfThenElse2.Eval1 by assumption. reflexivity. }
      assert ((f!:(r,x):) = y) as H23. { rewrite H15, H16 in H22. assumption. }
      assert (FunctionOn f (:P(a :x: a) :x: :P(a))) as H24. {
        rewrite H3. apply IfThenElse2.IsFunctionOn. }
      apply (FunctionOn.RangeCharac f (:P(a :x: a) :x: :P(a))). 1: assumption.
      exists :(r,x):. split. 2: assumption.
      apply Prod.Charac2. split; assumption. }
  exists (range f). assumption.
Qed.
