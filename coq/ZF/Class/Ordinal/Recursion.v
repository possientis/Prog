Require Import ZF.Class.Equiv.
Require Import ZF.Class.Ordinal.Core.
Require Import ZF.Class.Ordinal.Induction.
Require Import ZF.Class.Ordinal.Transitive.
Require Import ZF.Class.Relation.Domain.
Require Import ZF.Class.Relation.Function.
Require Import ZF.Class.Relation.Functional.
Require Import ZF.Class.Relation.Relation.
Require Import ZF.Class.Small.
Require Import ZF.Set.Core.
Require Import ZF.Set.Foundation.
Require Import ZF.Set.Incl.
Require Import ZF.Set.Inter2.
Require Import ZF.Set.OrdPair.
Require Import ZF.Set.Ordinal.Core.
Require Import ZF.Set.Ordinal.Succ.
Require Import ZF.Set.Relation.Eval.
Require Import ZF.Set.Relation.FunctionOn.
Require Import ZF.Set.Relation.Restrict.
Require Import ZF.Set.Single.
Require Import ZF.Set.Union2.

(* Transfinite recursion class associated with a class F.                       *)
Definition Recursion (F:Class) : Class := fun x => exists f, exists a,
  x :< f                                  /\
  On a                                    /\
  FunctionOn f a                          /\
  (forall b, b :< a -> f!b = F!(f:|:b)).

Lemma Coincide : forall (F:Class) (f g a b:U),
  On a                                  ->
  On b                                  ->
  a :<=: b                              ->
  FunctionOn f a                        ->
  FunctionOn g b                        ->
  (forall x, x :< a -> f!x = F!(f:|:x)) ->
  (forall x, x :< b -> g!x = F!(g:|:x)) ->
  (forall x, x :< a -> f!x = g!x).
Proof.
  intros F f g a b H1 H2 H3 H4 H5 H6 H7.
  remember (fun x => On x /\ (x :< a -> f!x = g!x)) as A eqn:H8.
  assert (A :~: On) as H9. {
    apply Induction.
    - intros x H9. rewrite H8 in H9. apply H9.
    - intros c H9 H10. rewrite H8. split. 1: assumption. intros H11.
      assert (f:|:c = g:|:c) as H12. {
        assert (c :<=: a) as H12. {
          apply ZF.Set.Ordinal.Core.LessIsElem; assumption. }
        apply FunctionOn.RestrictEqual with a b; try assumption.
        + apply Incl.Tran with a; assumption.
        + intros x H13.
          assert (A x) as H14. { apply H10. assumption. }
          rewrite H8 in H14. destruct H14 as [H14 H15].
          apply H15, H12. assumption. }
          rewrite H6, H7, H12. 1: reflexivity. 2: assumption.
          apply H3. assumption. }
  intros x H10.
  assert (On x) as H11. { apply ZF.Set.Ordinal.Core.IsOrdinal with a; assumption. }
  assert (A x) as H12. { apply H9. assumption. }
  rewrite H8 in H12. destruct H12 as [_ H12]. apply H12. assumption.
Qed.

(* The transfinite recursion class associated with F is a relation.             *)
Proposition IsRelation : forall (F:Class), Relation (Recursion F).
Proof.
  intros F x H1. destruct H1 as [f [b [H1 [_ [[[H2 _] _] _]]]]].
  specialize (H2 x H1). assumption.
Qed.

(* The transfinite recursion class associated with F is a function.             *)
Proposition IsFunction : forall (F:Class), Function (Recursion F).
Proof.
  intros F. split. 1: apply IsRelation. intros x y z H1 H2.
  destruct H1 as [f [a [H1 [H3 [H4 H5]]]]].
  destruct H2 as [g [b [H2 [H6 [H7 H8]]]]].
  assert (a :<=: b \/ b :<=: a) as H9. {
    apply ZF.Set.Ordinal.Core.InclOrIncl; assumption. }
  assert (x :< a) as H10. {
    destruct H4 as [_ H4]. rewrite <- H4.
    apply Domain.Charac. exists y. assumption. }
  assert (x :< b) as H11. {
    destruct H7 as [_ H7]. rewrite <- H7.
    apply Domain.Charac. exists z. assumption. }
  assert (f!x = y) as H12. { apply (FunctionOn.EvalCharac f a); assumption. }
  assert (g!x = z) as H13. { apply (FunctionOn.EvalCharac g b); assumption. }
  rewrite <- H12, <- H13. destruct H9 as [H9|H9].
  - apply Coincide with F a b; assumption.
  - symmetry. apply Coincide with F b a; assumption.
Qed.

(* The domain of the transfinite recursion class is an Ordinal class.           *)
Lemma DomainIsOrdinal : forall (F:Class),
  Class.Ordinal.Core.Ordinal (domain (Recursion F)).
Proof.
  intros F.
  assert (Transitive (domain (Recursion F))) as H1. {
    intros x [y [f [a [H1 [H2 [H3 H4]]]]]] u H5.
    assert (x :< a) as H6. {
      destruct H3 as [_ H3]. rewrite <- H3. apply ZF.Set.Relation.Domain.Charac.
      exists y. assumption. }
    assert (toClass a :<=: domain (Recursion F)) as H7. {
      intros v H7. exists (f!v). exists f. exists a. split.
      - apply FunctionOn.Satisfies with a; assumption.
      - split. 1: assumption. split; assumption. }
    apply H7.
    assert (On x) as H8. {
      apply ZF.Set.Ordinal.Core.IsOrdinal with a; assumption. }
    apply ZF.Set.Ordinal.Core.IfElemThenIncl in H6; try assumption.
    apply H6. assumption. }
  assert (domain (Recursion F) :<=: On) as H2. {
    intros x [y [f [a [H2 [H3 [H4 H5]]]]]].
    assert (x :< a) as H6. {
      destruct H4 as [_ H4]. rewrite <- H4. apply ZF.Set.Relation.Domain.Charac.
      exists y. assumption. }
    apply ZF.Set.Ordinal.Core.IsOrdinal with a; assumption. }
  apply TransitiveInclIsOrdinal with On; try assumption. apply OnIsOrdinal.
Qed.

(* The domain of the transfinite recursion class is the class of ordinals       *)
Proposition DomainIsOn : forall (F:Class), domain (Recursion F) :~: On.
Proof.
  intros F.
  assert (
    domain (Recursion F) :~: On                           \/
    exists a, On a /\ domain (Recursion F) :~: toClass a) as H1. {
      apply IsOnOrOrdinalSet. apply DomainIsOrdinal. }
  destruct H1 as [H1|H1]. 1: assumption. exfalso. destruct H1 as [c [H1 H2]].
  assert (Small (Recursion F)) as H3. {
    apply Function.IsSmall.
    - apply IsFunction.
    - apply IsSomeSet. exists c. assumption. }
  apply IsSomeSet in H3. destruct H3 as [f H3].
  assert (ZF.Set.Relation.Domain.domain f = c) as H4. {
    apply DoubleInclusion. split; intros x H4.
    - apply Domain.ToClass in H4. apply H2.
      apply Domain.EquivCompat with (toClass f); assumption.
    - apply H2 in H4. apply Domain.ToClass.
      apply Domain.EquivCompat with (Recursion F). 2: assumption.
      apply Equiv.Sym. assumption. }
  assert (ZF.Set.Relation.Relation.Relation f) as H5. {
    apply Relation.ToClass. apply Relation.EquivCompat with (Recursion F).
    1: assumption. apply IsRelation. }
  assert  (ZF.Set.Relation.Functional.Functional f) as H6. {
    apply Functional.ToClass. apply Functional.EquivCompat with (Recursion F).
    1: assumption. apply IsFunction. }
  assert (ZF.Set.Relation.Function.Function f) as H7. { split; assumption. }
  assert (FunctionOn f c) as H8. { split; assumption. }
  remember (fun f a =>
    On a                                    /\
    FunctionOn f a                          /\
    (forall b, b :< a -> f!b = F!(f:|:b))) as K eqn:H9.
  assert (forall x y, :(x,y): :< f <-> exists g a, :(x,y): :< g /\ K g a) as H10. {
    intros x y. split; intros H10.
    - apply H3 in H10. destruct H10 as [g [a [H10 [H11 [H12 H13]]]]].
      exists g. exists a. split. 1: assumption. rewrite H9.
      split. 1: assumption. split; assumption.
    - destruct H10 as [g [a [H10 H11]]]. rewrite H9 in H11.
      destruct H11 as [H11 [H12 H13]]. apply H3. exists g. exists a.
      split. 1: assumption. split. 1: assumption. split; assumption. }
  assert (forall g a, K g a -> a :<=: c) as H11. {
    intros g a H11 x H12. assert (H13 := H11). rewrite H9 in H13.
    destruct H13 as [_ [[_ H13] _]]. rewrite <- H13 in H12.
    apply Domain.Charac in H12. destruct H12 as [y H12].
    assert (:(x,y): :< f) as H14. {
      apply H10. exists g. exists a. split; assumption. }
    rewrite <- H4. apply Domain.Charac. exists y. assumption. }
  assert (forall g a, K g a -> FunctionOn (f:|:a) a) as H12. {
    intros g a H12. apply (FunctionOn.Restrict f c a) in H8.
    assert (c :/\: a = a) as H13. {
      apply Inter2.WhenInclR. apply H11 with g. assumption. }
    rewrite H13 in H8. assumption. }
  assert (forall g a, K g a -> g = f:|:a) as H13. {
    intros g a H13. assert (H14 := H13). rewrite H9 in H14.
    destruct H14 as [H14 [H15 H16]].
    apply FunctionOn.EqualCharac with a a. 1: assumption.
    - apply H12 with g. assumption.
    - reflexivity.
    - intros x H17.
      assert ((f:|:a)!x = f!x) as H18. {
        apply Restrict.Eval. 2: assumption.
        destruct H8 as [[_ H8] _]. assumption. }
      rewrite H18. symmetry. apply (FunctionOn.EvalCharac f c). 1: assumption.
      apply (H11 g a); try assumption. apply H10. exists g. exists a. split.
      2: assumption. apply FunctionOn.Satisfies with a; assumption. }
  assert (forall b, b :< c -> f!b = F!(f:|:b)) as H14. {
    intros b H14.
    assert (:(b,f!b): :< f) as H15. {
      apply FunctionOn.Satisfies with c; assumption. }
    apply H10 in H15. destruct H15 as [g [a [H15 H16]]].
    assert (H17 := H16). rewrite H9 in H17. destruct H17 as [H17 [H18 H19]].
    assert (b :< a) as H20. {
      destruct H18 as [_ H18]. rewrite <- H18. apply Domain.Charac.
      exists f!b. assumption. }
    assert (f!b = g!b) as H21. {
      symmetry. apply (FunctionOn.EvalCharac g a); assumption. }
    assert (g = f:|:a) as H22. { apply H13. assumption. }
    assert (g:|:b = f:|:b) as H23. {
      rewrite H22. apply Restrict.TowerProperty.
      apply ZF.Set.Ordinal.Core.IfElemThenIncl; try assumption.
      apply ZF.Set.Ordinal.Core.IsOrdinal with a; assumption. }
    rewrite H21, <- H23. apply H19. assumption. }
  remember (f :\/: :{ :(c,F!f): }:) as g eqn:H15.
  assert (ZF.Set.Relation.Relation.Relation g) as H16. {
    intros x H16. rewrite H15 in H16. apply Union2.Charac in H16.
    destruct H16 as [H16|H16].
    - apply H5 in H16. assumption.
    - apply Single.Charac in H16. exists c. exists F!f. assumption. }
  assert (ZF.Set.Relation.Function.Function g) as H17. {
    split. 1: apply H16. intros x y z H17 H18.
    rewrite H15 in H17. rewrite H15 in H18.
    apply Union2.Charac in H17. apply Union2.Charac in H18.
    destruct H17 as [H17|H17]; destruct H18 as [H18|H18].
    - apply H6 with x; assumption.
    - exfalso. apply Single.Charac in H18. apply OrdPair.WhenEqual in H18.
      destruct H18 as [H18 _]. rewrite H18 in H17.
      assert (c :< ZF.Set.Relation.Domain.domain f) as H19. {
        apply Domain.Charac. exists y. assumption. }
      rewrite H4 in H19. apply NoElemLoop1 with c. assumption.
    - exfalso. apply Single.Charac in H17. apply OrdPair.WhenEqual in H17.
      destruct H17 as [H17 _]. rewrite H17 in H18.
      assert (c :< ZF.Set.Relation.Domain.domain f) as H19. {
        apply Domain.Charac. exists z. assumption. }
      rewrite H4 in H19. apply NoElemLoop1 with c. assumption.
    - apply Single.Charac in H17. apply Single.Charac in H18.
      apply OrdPair.WhenEqual in H17. apply OrdPair.WhenEqual in H18.
      destruct H17 as [_ H17]. destruct H18 as [_ H18]. subst. reflexivity. }
  assert (FunctionOn g (succ c)) as H18. {
    split. 1: assumption. apply DoubleInclusion. split; intros x H18.
    - apply Domain.Charac in H18. destruct H18 as [y H18].
      rewrite H15 in H18. apply Union2.Charac in H18. apply Union2.Charac.
      destruct H18 as [H18|H18].
      + left. rewrite <- H4. apply Domain.Charac. exists y. assumption.
      + right. apply Single.Charac in H18. apply OrdPair.WhenEqual in H18.
        destruct H18 as [H18 _]. apply Single.Charac. assumption.
    - apply Domain.Charac. apply Union2.Charac in H18. destruct H18 as [H18|H18].
      + rewrite <- H4 in H18. apply Domain.Charac in H18. destruct H18 as [y H18].
        exists y. rewrite H15. apply Union2.Charac. left. assumption.
      + apply Single.Charac in H18. exists F!f. rewrite H15.
        apply Union2.Charac. right. rewrite H18. apply Single.IsIn. }
  assert (g:|:c = f) as H19. {
    apply FunctionOn.EqualCharac with c c. 2: assumption.
    - assert (succ c :/\: c = c) as H19. {
        apply Inter2.WhenInclR, Succ.IsIncl. }
      assert (FunctionOn (g:|:c) (succ c :/\: c)) as H20. {
        apply FunctionOn.Restrict. assumption. }
      rewrite H19 in H20. assumption.
    - reflexivity.
    - intros x H19.
      assert ((g:|:c)!x = g!x) as H20. {
        apply Restrict.Eval. 2: assumption. destruct H18 as [[_ H18] _].
        assumption. }
      rewrite H20. apply (FunctionOn.EvalCharac g (succ c)). 1: assumption.
      + apply Union2.Charac. left. assumption.
      + rewrite H15. apply Union2.Charac. left.
        apply FunctionOn.Satisfies with c; assumption. }
  assert (forall b, b :< succ c -> g!b = F!(g:|:b)) as H20. {
    intros b H20. apply Union2.Charac in H20. destruct H20 as [H20|H20].
    - assert (g!b = f!b) as H21. {
        rewrite <- H19. symmetry. apply Restrict.Eval. 2: assumption.
        destruct H18 as [[_ H18] _]. assumption. }
      assert (g:|:b = f:|:b) as H22. {
        rewrite <- H19. symmetry. apply Restrict.TowerProperty.
        apply ZF.Set.Ordinal.Core.IfElemThenIncl; try assumption.
        apply ZF.Set.Ordinal.Core.IsOrdinal with c; assumption. }
      rewrite H21, H22. apply H14. assumption.
    - apply Single.Charac in H20.
      assert (g!b = F!f) as H21. {
        apply (FunctionOn.EvalCharac g (succ c)). 1: assumption.
        + apply Union2.Charac. right. rewrite H20. apply Single.IsIn.
        + rewrite H20, H15. apply Union2.Charac. right. apply Single.IsIn. }
      rewrite H21, H20, H19. reflexivity. }
  assert (K g (succ c)) as H21. {
    rewrite H9. split.
    - apply Succ.IsOrdinal. assumption.
    - split; assumption. }
  assert (:(c, F!f): :< f) as H22. {
    apply H10. exists g. exists (succ c). split. 2: assumption.
    rewrite H15. apply Union2.Charac. right. apply Single.IsIn. }
  assert (c :< ZF.Set.Relation.Domain.domain f) as H23. {
    apply Domain.Charac. exists F!f. assumption. }
  rewrite H4 in H23. apply NoElemLoop1 with c. assumption.
Qed.
