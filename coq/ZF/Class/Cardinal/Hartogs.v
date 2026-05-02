Require Import ZF.Axiom.Classic.
Require Import ZF.Class.Cardinal.Isom.
Require Import ZF.Class.Equiv.
Require Import ZF.Class.Small.
Require Import ZF.Set.Core.
Require Import ZF.Set.Incl.
Require Import ZF.Set.Empty.
Require Import ZF.Set.Order.E.
Require Import ZF.Set.Order.Isom.
Require Import ZF.Set.Order.WellOrdering.
Require Import ZF.Set.Ordinal.Core.
Require Import ZF.Set.OrdPair.
Require Import ZF.Set.Power.
Require Import ZF.Set.Prod.
Require Import ZF.Set.Relation.Bij.
Require Import ZF.Set.Relation.BijectionOn.
Require Import ZF.Set.Relation.Converse.
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
      (fun p => (isom!:(fst p,snd p):) :[snd p]:) (fun _ => :0:)) as f eqn:H3.
  assert (forall y, y :< range f <-> hartogs a y) as H4. {
    intros y. split; intros H4.
    - apply (FunctionOn.RangeCharac f (:P(a :x: a) :x: :P(a))) in H4.
      2: { rewrite H3. apply IfThenElse2.IsFunctionOn. }
      destruct H4 as [u [H4 H5]]. apply Prod.Charac in H4.
      destruct H4 as [r [x [H4 [H6 H7]]]]. rewrite H4 in H5. clear H4.
      assert (WO :(r,x): \/ ~ WO :(r,x):) as [H8|H8]. { apply LawExcludedMiddle. }
      + assert ((f!:(r,x):) = (isom!:(r,x):) :[x]:) as H9. {
          rewrite H3. apply IfThenElse2.Eval1; assumption. }
        unfold hartogs.
        assert (Ordinal y) as H10. {
          rewrite <- H5, H9. apply Isom.IsOrdinal, H2. assumption. }
        remember (isom!:(r,x):) as g eqn:H11.
        assert (Isom g r (E y) x y) as H12. {
          rewrite H11. apply Isom.IsIsom.
          - apply H2. assumption.
          - rewrite H5, H11 in H9. assumption. }
        assert (Bij g^:-1: y x) as H13. { apply Bij.Converse, H12. }
        assert (Inj g^:-1: y a) as H14. {
          split.
          - apply H13.
          - assert (range g^:-1: = x) as H14. { apply H13. }
            rewrite H14. apply Power.Charac. assumption. }
        split. 1: assumption. exists g^:-1:. assumption.
      + assert ((f!:(r,x):) = :0:) as H9. {
          rewrite H3. apply IfThenElse2.Eval2; assumption. }
        assert (y = :0:) as H10. { rewrite <- H5, H9. reflexivity. }
        unfold hartogs. rewrite H10. split.
        * apply Core.ZeroIsOrdinal.
        * exists :0:. apply Inj.WhenEmpty. reflexivity.
    - destruct H4 as [H4 [i H5]].
      remember (range i) as x eqn:H6.
      assert (x :<=: a) as H7. { rewrite H6. apply H5. }
      assert (Bij i y x) as H8. {
        split.
        - apply H5.
        - symmetry. assumption. }
(*
      remember (i^:-1:) as j eqn:H9.
      assert (Bij j x y) as H10. { rewrite H9. apply Bij.Converse. assumption. }
      remember {{x :< x :x: x
                | fun z => exists u v, z = :(u,v): /\ j!u :< j!v}} as r eqn:H12.
      assert (forall u v,
        :(u,v): :< r <-> u :< x /\ v :< x /\ j!u :< j!v) as H13. {
          intros u v. split; intros H13.
          - rewrite H12 in H13. apply Specify.Charac in H13.
            destruct H13 as [H13 H14].
            apply Prod.Charac2 in H13. destruct H13 as [H13 H15].
            destruct H14 as [u' [v' [H14 H16]]].
            apply OrdPair.WhenEqual in H14. destruct H14 as [H14 H17].
            split. 1: assumption. split. 1: assumption.
            rewrite H14, H17. assumption.
          - destruct H13 as [H13 [H14 H15]]. rewrite H12.
            apply Specify.Charac. split.
            + apply Prod.Charac2. split; assumption.
            + exists u, v. split. 2: assumption. reflexivity. }
      assert (FunctionOn f (:P(a :x: a) :x: :P(a))) as H14. {
        rewrite H3. apply IfThenElse2.IsFunctionOn. }
      apply (FunctionOn.RangeCharac f (:P(a :x: a) :x: :P(a))). 1: assumption.
      exists :(r,x):.
      assert (r :< :P(a :x: a)) as H15. {
        apply Power.Charac. intros z H15. rewrite H12 in H15.
        apply Specify.Charac in H15. destruct H15 as [H15 _].
        apply Prod.Charac in H15. destruct H15 as [u [v [H15 [H16 H17]]]].
        apply Prod.Charac. exists u, v. split. 1: assumption.
        split; apply H7; assumption. }
      assert (x :< :P(a)) as H16. { apply Power.Charac. assumption. }
      assert (:(r,x): :< :P(a :x: a) :x: :P(a)) as H17. {
        apply Prod.Charac2. split; assumption. }
      split. 1: assumption.
      assert (WO :(r,x):) as H18. {
        apply H2.
*)
Admitted.
