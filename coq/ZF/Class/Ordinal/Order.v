Require Import ZF.Class.Equiv.
Require Import ZF.Class.Diff.
Require Import ZF.Class.Empty.
Require Import ZF.Class.Incl.
Require Import ZF.Class.Inter2.
Require Import ZF.Class.IsSetOf.
Require Import ZF.Class.Less.
Require Import ZF.Class.Order.E.
Require Import ZF.Class.Order.Isom.
Require Import ZF.Class.Order.Minimal.
Require Import ZF.Class.Ordinal.Core.
Require Import ZF.Class.Ordinal.Inf.
Require Import ZF.Class.Ordinal.Transfinite.
Require Import ZF.Class.Ordinal.Transitive.
Require Import ZF.Class.Relation.Bij.
Require Import ZF.Class.Relation.Compose.
Require Import ZF.Class.Relation.Converse.
Require Import ZF.Class.Relation.Functional.
Require Import ZF.Set.Core.
Require Import ZF.Set.Foundation.
Require Import ZF.Set.Incl.
Require Import ZF.Set.Ordinal.InfOfClass.
Require Import ZF.Set.OrdPair.
Require Import ZF.Set.Relation.EvalOfClass.
Require Import ZF.Set.Relation.ImageByClass.


(* An element a of an ordinal class A is a :<-minimal element of A\a.           *)
Proposition IsEMinimal : forall (A:Class) (a:U),
  Ordinal A ->
  A a       ->
  Minimal E (A :\: toClass a) a.
Proof.
  intros A a H1 H2.
  assert (On a) as H3. { apply Class.Ordinal.Core.IsOrdinal with A; assumption. }
  assert (A :\: toClass a :<>: :0:) as H4. {
    apply Class.Empty.HasElem. exists a. split. 1: assumption. apply NoElemLoop1. }
  apply Inf.IsEMinimal. 2: assumption.
  - intros x [H5 _]. apply Class.Ordinal.Core.IsOrdinal with A; assumption.
  - apply Inf.WhenOrdinal; assumption.
Qed.

Proposition IsId : forall (F A B:Class),
  Ordinal A       ->
  Ordinal B       ->
  Isom F E E A B  ->
  forall (a:U), A a -> F!a = a.
Proof.
  intros F A B H1 H2 H3.
  remember (fun a => On a /\ (A a -> F!a = a)) as C eqn:H4.
  assert (C :~: On) as H5. {
    apply Transfinite.Induction.
    - intros a H5. rewrite H4 in H5. destruct H5 as [H5 _]. assumption.
    - intros b H5 H6. rewrite H4. split. 1: assumption. intros H7.
      assert (forall a, a :< b -> F!a = a) as H8. {
        intros a H8.
        assert (C a) as H9. { apply H6. assumption. }
        rewrite H4 in H9. destruct H9 as [H9 H10]. apply H10.
        assert (H11 := H1). destruct H11 as [H11 _].
        apply H11 with b; assumption. }
      clear H4 H6 C.
      assert (F:[b]: = b) as H9. {
        apply DoubleInclusion. split; intros a H9.
        - apply (Bij.ImageSetCharac F A B) in H9. 2: apply H3.
          destruct H9 as [x [H9 [H10 H11]]].
          assert (F!x = x) as H12. { apply H8. assumption. }
          rewrite H11 in H12. rewrite H12. assumption.
        - apply (Bij.ImageSetCharac F A B). 1: apply H3.
          exists a. split. 1: assumption. split.
          + destruct H1 as [H1 _]. apply (H1 b); assumption.
          + apply H8, H9. }
      assert (Minimal E (A :\: toClass b) b) as H10. {
        apply IsEMinimal; assumption. }
      assert (Minimal E F:[A :\: toClass b]: (F!b)) as H11. {
        apply Minimal.IsomImage with E A B; try assumption.
        apply Inter2.IsInclL. }
      clear H10.
      assert (F:[A :\: toClass b]: :~: B :\: toClass b) as H12. {
        apply Equiv.Tran with (F:[A]: :\: F:[toClass b]:).
        - apply Bij.DiffImage with A B, H3.
        - apply Diff.EquivCompat.
          + apply Bij.ImageOfDomain, H3.
          + apply Equiv.Tran with (toClass F:[b]:).
            * apply Equiv.Sym, ImageByClass.ToClass, H3.
            * apply EqualToClass. assumption. }
      assert (Minimal E (B :\: toClass b) (F!b)) as H13. {
        apply Minimal.EquivCompatR with F:[A :\: toClass b]:; assumption. }
      clear H11 H12.
      assert (B b) as H14. {
        apply Class.Ordinal.Core.LessIsElem; try assumption. split.
        - intros a H14. apply (Bij.ImageOfDomain F A B). 1: apply H3.
          apply (Bij.ImageCharac F A B). 1: apply H3.
          exists a. assert (A a) as H15. {
            destruct H1 as [H1 _]. apply (H1 b); assumption. }
          split. 1: assumption. split. 1: assumption. apply H8, H14.
        - apply Equiv.NotSym, Diff.WhenNotEmpty, Class.Empty.HasElem.
          exists F!b. apply Minimal.IsIn with E. assumption. }
      assert (Minimal E (B :\: toClass b) b) as H15. {
        apply IsEMinimal; assumption. }
      assert (B :\: toClass b :<=: On) as H16. {
        intros a [H16 _]. apply Class.Ordinal.Core.IsOrdinal with B; assumption. }
      assert (B :\: toClass b :<>: :0:) as H17. {
        apply Class.Empty.HasElem. exists b. split. 1: assumption.
        apply NoElemLoop1. }
      assert (b = inf (B :\: toClass b)) as H18. {
        apply InfOfClass.IsEMinimal; assumption. }
      assert (F!b = inf (B :\: toClass b)) as H19. {
        apply InfOfClass.IsEMinimal; assumption. }
      rewrite <- H18 in H19. assumption. }
  intros a H6.
  assert (On a) as H7. { apply Class.Ordinal.Core.IsOrdinal with A; assumption. }
  assert (C a) as H8. { apply H5. assumption. }
  rewrite H4 in H8. destruct H8 as [_ H8]. apply H8. assumption.
Qed.

(* Two isomorphic ordinal classes are in fact equal.                            *)
Proposition IsEquiv : forall (F A B:Class),
  Ordinal A       ->
  Ordinal B       ->
  Isom F E E A B  ->
  A :~: B.
Proof.
  intros F A B H1 H2 H3.
  assert (F:[A]: :~: B) as H4. { apply Bij.ImageOfDomain, H3. }
  intros a. split; intros H5.
  - apply H4. apply (Bij.ImageCharac F A B). 1: apply H3. exists a.
    split. 1: assumption. split. 1: assumption. apply IsId with A B; assumption.
  - apply H4 in H5. apply (Bij.ImageCharac F A B) in H5. 2: apply H3.
    destruct H5 as [x [H5 [_ H7]]].
    assert (F!x = x) as H8. { apply IsId with A B; assumption. }
    rewrite H7 in H8. rewrite H8. assumption.
Qed.

(* An R-ordered class C is isomorphic to at most one ordinal class.             *)
Proposition IsEquivGen : forall (F G R A B C:Class),
  Ordinal A       ->
  Ordinal B       ->
  Isom F E R A C  ->
  Isom G E R B C  ->
  A :~: B.
Proof.
  intros F G R A B C H1 H2 H3 H4. apply IsEquiv with (G^:-1: :.: F);
  try assumption. apply Isom.Compose with R C. 1: assumption.
  apply Isom.Converse. assumption.
Qed.
