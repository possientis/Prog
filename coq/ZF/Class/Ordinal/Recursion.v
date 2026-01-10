Require Import ZF.Class.Equiv.
Require Import ZF.Class.Ordinal.Core.
Require Import ZF.Class.Ordinal.Induction.
Require Import ZF.Class.Ordinal.Transitive.
Require Import ZF.Class.Relation.Domain.
Require Import ZF.Class.Relation.Function.
Require Import ZF.Class.Relation.Functional.
Require Import ZF.Class.Relation.FunctionOn.
Require Import ZF.Class.Relation.Relation.
Require Import ZF.Class.Small.
Require Import ZF.Set.Core.
Require Import ZF.Set.Foundation.
Require Import ZF.Set.Incl.
Require Import ZF.Set.Inter2.
Require Import ZF.Set.OrdPair.
Require Import ZF.Set.Ordinal.Core.
Require Import ZF.Set.Ordinal.Succ.
Require Import ZF.Set.Relation.Domain.
Require Import ZF.Set.Relation.Eval.
Require Import ZF.Set.Relation.EvalOfClass.
Require Import ZF.Set.Relation.Function.
Require Import ZF.Set.Relation.FunctionOn.
Require Import ZF.Set.Relation.Relation.
Require Import ZF.Set.Relation.Restrict.
Require Import ZF.Set.Relation.RestrictOfClass.
Require Import ZF.Set.Single.
Require Import ZF.Set.Union2.

Module COC := ZF.Class.Ordinal.Core.
Module CRD := ZF.Class.Relation.Domain.
Module CRF := ZF.Class.Relation.Function.
Module CFL := ZF.Class.Relation.Functional.
Module CFO := ZF.Class.Relation.FunctionOn.
Module CRR := ZF.Class.Relation.Relation.

Module SOC := ZF.Set.Ordinal.Core.
Module SRD := ZF.Set.Relation.Domain.
Module SRF := ZF.Set.Relation.Function.
Module SFL := ZF.Set.Relation.Functional.
Module SFO := ZF.Set.Relation.FunctionOn.
Module SRR := ZF.Set.Relation.Relation.

(* Transfinite recursion class associated with a class F. In other words, the   *)
(* unique function class G defined on On by the recursion G(b) = F(G|b).        *)
Definition Recursion (F:Class) : Class := fun x => exists f a,
  x :< f                                  /\
  On a                                    /\
  SFO.FunctionOn f a                      /\
  (forall b, b :< a -> f!b = F!(f:|:b)).

(* Binary predicate underlying the transfinite recursion class.                 *)
Definition K (F:Class) : U -> U -> Prop := fun f a =>
  On a                /\
  SFO.FunctionOn f a  /\
  (forall b, b :< a -> f!b = F!(f:|:b)).

Lemma Charac2 : forall (F:Class) (x y:U),
  Recursion F :(x,y): <-> exists f a, :(x,y): :< f /\ K F f a.
Proof.
  intros F x y. split; intros H1; destruct H1 as [f [a [H1 H2]]];
  exists f; exists a; split; assumption.
Qed.

(* Two recursive functions coincide on their common domain.                     *)
Lemma Coincide : forall (F:Class) (f g a b:U),
  On a                                  ->
  On b                                  ->
  a :<=: b                              ->
  SFO.FunctionOn f a                    ->
  SFO.FunctionOn g b                    ->
  (forall x, x :< a -> f!x = F!(f:|:x)) ->
  (forall x, x :< b -> g!x = F!(g:|:x)) ->
  (forall x, x :< a -> f!x = g!x).
Proof.
  intros F f g a b H1 H2 H3 H4 H5 H6 H7.
  remember (fun x => On x /\ (x :< a -> f!x = g!x)) as A eqn:H8.
  assert (A :~: On) as H9. {
    apply Induction.Induction1.
    - intros x H9. rewrite H8 in H9. apply H9.
    - intros c H9 H10. rewrite H8. split. 1: assumption. intros H11.
      assert (f:|:c = g:|:c) as H12. {
        assert (c :<=: a) as H12. {
          apply SOC.LessIsElem; assumption. }
        apply SFO.RestrictEqual with a b; try assumption.
        + apply Incl.Tran with a; assumption.
        + intros x H13.
          assert (A x) as H14. { apply H10. assumption. }
          rewrite H8 in H14. destruct H14 as [H14 H15].
          apply H15, H12. assumption. }
          rewrite H6, H7, H12. 1: reflexivity. 2: assumption.
          apply H3. assumption. }
  intros x H10.
  assert (On x) as H11. { apply SOC.IsOrdinal with a; assumption. }
  assert (A x) as H12. { apply H9. assumption. }
  rewrite H8 in H12. destruct H12 as [_ H12]. apply H12. assumption.
Qed.

(* The transfinite recursion class associated with F is a relation.             *)
Proposition IsRelation : forall (F:Class), CRR.Relation (Recursion F).
Proof.
  intros F x H1. destruct H1 as [f [a [H1 [_ [[[H2 _] _] _]]]]].
  specialize (H2 x H1). assumption.
Qed.

(* The transfinite recursion class associated with F is a function.             *)
Proposition IsFunction : forall (F:Class), CRF.Function (Recursion F).
Proof.
  intros F. split. 1: apply IsRelation. intros x y z H1 H2.
  destruct H1 as [f [a [H1 [H3 [H4 H5]]]]].
  destruct H2 as [g [b [H2 [H6 [H7 H8]]]]].
  assert (a :<=: b \/ b :<=: a) as H9. {
    apply SOC.InclOrIncl; assumption. }
  assert (x :< a) as H10. {
    destruct H4 as [_ H4]. rewrite <- H4.
    apply SRD.Charac. exists y. assumption. }
  assert (x :< b) as H11. {
    destruct H7 as [_ H7]. rewrite <- H7.
    apply SRD.Charac. exists z. assumption. }
  assert (f!x = y) as H12. { apply (SFO.EvalCharac f a); assumption. }
  assert (g!x = z) as H13. { apply (SFO.EvalCharac g b); assumption. }
  rewrite <- H12, <- H13. destruct H9 as [H9|H9].
  - apply Coincide with F a b; assumption.
  - symmetry. apply Coincide with F b a; assumption.
Qed.

(* The domain of the transfinite recursion class is an Ordinal class.           *)
Lemma DomainIsOrdinal : forall (F:Class),
  COC.Ordinal (CRD.domain (Recursion F)).
Proof.
  intros F.
  assert (Transitive (CRD.domain (Recursion F))) as H1. {
    intros x [y [f [a [H1 [H2 [H3 H4]]]]]] u H5.
    assert (x :< a) as H6. {
      destruct H3 as [_ H3]. rewrite <- H3. apply SRD.Charac.
      exists y. assumption. }
    assert (toClass a :<=: CRD.domain (Recursion F)) as H7. {
      intros v H7. exists (f!v). exists f. exists a. split.
      - apply SFO.Satisfies with a; assumption.
      - split. 1: assumption. split; assumption. }
    apply H7.
    assert (On x) as H8. {
      apply SOC.IsOrdinal with a; assumption. }
    apply SOC.ElemIsIncl in H6; try assumption.
    apply H6. assumption. }
  assert (CRD.domain (Recursion F) :<=: On) as H2. {
    intros x [y [f [a [H2 [H3 [H4 H5]]]]]].
    assert (x :< a) as H6. {
      destruct H4 as [_ H4]. rewrite <- H4. apply SRD.Charac.
      exists y. assumption. }
    apply SOC.IsOrdinal with a; assumption. }
  apply TransitiveInclIsOrdinal with On; try assumption. apply OnIsOrdinal.
Qed.

(* The domain of the transfinite recursion class is the class of ordinals       *)
Proposition DomainIsOn : forall (F:Class), CRD.domain (Recursion F) :~: On.
Proof.
  intros F.
  assert (
    CRD.domain (Recursion F) :~: On                           \/
    exists a, On a /\ CRD.domain (Recursion F) :~: toClass a) as H1. {
      apply IsOnOrOrdinalSet. apply DomainIsOrdinal. }
  destruct H1 as [H1|H1]. 1: assumption. exfalso. destruct H1 as [c [H1 H2]].
  assert (Small (Recursion F)) as H3. {
    apply Function.IsSmall.
    - apply IsFunction.
    - apply IsSomeSet. exists c. assumption. }
  apply IsSomeSet in H3. destruct H3 as [f H3].
  assert (SRD.domain f = c) as H4. {
    apply DoubleInclusion. split; intros x H4.
    - apply SRD.ToClass in H4. apply H2.
      apply CRD.EquivCompat with (toClass f); assumption.
    - apply H2 in H4. apply SRD.ToClass.
      apply CRD.EquivCompat with (Recursion F). 2: assumption.
      apply Equiv.Sym. assumption. }
  assert (SRR.Relation f) as H5. {
    apply Relation.ToClass. apply Relation.EquivCompat with (Recursion F).
    1: assumption. apply IsRelation. }
  assert  (SFL.Functional f) as H6. {
    apply SFL.ToClass. apply CFL.EquivCompat with (Recursion F).
    1: assumption. apply IsFunction. }
  assert (SRF.Function f) as H7. { split; assumption. }
  assert (SFO.FunctionOn f c) as H8. { split; assumption. }
  remember (K F) as K' eqn:H9.
  assert (
    forall x y, :(x,y): :< f <-> exists g a, :(x,y): :< g /\ K' g a) as H10. {
    intros x y. rewrite H9. split; intros H10.
    - apply (proj1 (Charac2 _ _ _)), H3. assumption.
    - apply Charac2 in H10. apply H3 in H10. assumption. }
  assert (forall g a, K' g a -> a :<=: c) as H11. {
    intros g a H11 x H12. assert (H13 := H11). rewrite H9 in H13.
    destruct H13 as [_ [[_ H13] _]]. rewrite <- H13 in H12.
    apply SRD.Charac in H12. destruct H12 as [y H12].
    assert (:(x,y): :< f) as H14. {
      apply H10. exists g. exists a. split; assumption. }
    rewrite <- H4. apply SRD.Charac. exists y. assumption. }
  assert (forall g a, K' g a -> SFO.FunctionOn (f:|:a) a) as H12. {
    intros g a H12. apply (SFO.Restrict f c a). 1: assumption.
    apply H11 with g. assumption. }
  assert (forall g a, K' g a -> g = f:|:a) as H13. {
    intros g a H13. assert (H14 := H13). rewrite H9 in H14.
    destruct H14 as [H14 [H15 H16]].
    apply SFO.EqualCharac with a a. 1: assumption.
    - apply H12 with g. assumption.
    - reflexivity.
    - intros x H17.
      assert ((f:|:a)!x = f!x) as H18. {
        apply Restrict.Eval. 2: assumption.
        destruct H8 as [[_ H8] _]. assumption. }
      rewrite H18. symmetry. apply (SFO.EvalCharac f c). 1: assumption.
      apply (H11 g a); try assumption. apply H10. exists g. exists a. split.
      2: assumption. apply SFO.Satisfies with a; assumption. }
  assert (forall b, b :< c -> f!b = F!(f:|:b)) as H14. {
    intros b H14.
    assert (:(b,f!b): :< f) as H15. {
      apply SFO.Satisfies with c; assumption. }
    apply H10 in H15. destruct H15 as [g [a [H15 H16]]].
    assert (H17 := H16). rewrite H9 in H17. destruct H17 as [H17 [H18 H19]].
    assert (b :< a) as H20. {
      destruct H18 as [_ H18]. rewrite <- H18. apply SRD.Charac.
      exists f!b. assumption. }
    assert (f!b = g!b) as H21. {
      symmetry. apply (SFO.EvalCharac g a); assumption. }
    assert (g = f:|:a) as H22. { apply H13. assumption. }
    assert (g:|:b = f:|:b) as H23. {
      rewrite H22. apply Restrict.TowerProperty.
      apply SOC.ElemIsIncl; assumption. }
    rewrite H21, <- H23. apply H19. assumption. }
  remember (f :\/: :{ :(c,F!f): }:) as g eqn:H15.
  assert (SRR.Relation g) as H16. {
    intros x H16. rewrite H15 in H16. apply Union2.Charac in H16.
    destruct H16 as [H16|H16].
    - apply H5 in H16. assumption.
    - apply Single.Charac in H16. exists c. exists F!f. assumption. }
  assert (SRF.Function g) as H17. {
    split. 1: apply H16. intros x y z H17 H18.
    rewrite H15 in H17. rewrite H15 in H18.
    apply Union2.Charac in H17. apply Union2.Charac in H18.
    destruct H17 as [H17|H17]; destruct H18 as [H18|H18].
    - apply H6 with x; assumption.
    - exfalso. apply Single.Charac in H18. apply OrdPair.WhenEqual in H18.
      destruct H18 as [H18 _]. rewrite H18 in H17.
      assert (c :< SRD.domain f) as H19. {
        apply SRD.Charac. exists y. assumption. }
      rewrite H4 in H19. apply NoElemLoop1 with c. assumption.
    - exfalso. apply Single.Charac in H17. apply OrdPair.WhenEqual in H17.
      destruct H17 as [H17 _]. rewrite H17 in H18.
      assert (c :< SRD.domain f) as H19. {
        apply SRD.Charac. exists z. assumption. }
      rewrite H4 in H19. apply NoElemLoop1 with c. assumption.
    - apply Single.Charac in H17. apply Single.Charac in H18.
      apply OrdPair.WhenEqual in H17. apply OrdPair.WhenEqual in H18.
      destruct H17 as [_ H17]. destruct H18 as [_ H18]. subst. reflexivity. }
  assert (SFO.FunctionOn g (succ c)) as H18. {
    split. 1: assumption. apply DoubleInclusion. split; intros x H18.
    - apply SRD.Charac in H18. destruct H18 as [y H18].
      rewrite H15 in H18. apply Union2.Charac in H18. apply Union2.Charac.
      destruct H18 as [H18|H18].
      + left. rewrite <- H4. apply SRD.Charac. exists y. assumption.
      + right. apply Single.Charac in H18. apply OrdPair.WhenEqual in H18.
        destruct H18 as [H18 _]. apply Single.Charac. assumption.
    - apply SRD.Charac. apply Union2.Charac in H18. destruct H18 as [H18|H18].
      + rewrite <- H4 in H18. apply SRD.Charac in H18. destruct H18 as [y H18].
        exists y. rewrite H15. apply Union2.Charac. left. assumption.
      + apply Single.Charac in H18. exists F!f. rewrite H15.
        apply Union2.Charac. right. rewrite H18. apply Single.IsIn. }
  assert (g:|:c = f) as H19. {
    apply SFO.EqualCharac with c c. 2: assumption.
    - apply SFO.Restrict with (succ c). 1: assumption. apply Succ.IsIncl.
    - reflexivity.
    - intros x H19.
      assert ((g:|:c)!x = g!x) as H20. {
        apply Restrict.Eval. 2: assumption. destruct H18 as [[_ H18] _].
        assumption. }
      rewrite H20. apply (SFO.EvalCharac g (succ c)). 1: assumption.
      + apply Union2.Charac. left. assumption.
      + rewrite H15. apply Union2.Charac. left.
        apply SFO.Satisfies with c; assumption. }
  assert (forall b, b :< succ c -> g!b = F!(g:|:b)) as H20. {
    intros b H20. apply Union2.Charac in H20. destruct H20 as [H20|H20].
    - assert (g!b = f!b) as H21. {
        rewrite <- H19. symmetry. apply Restrict.Eval. 2: assumption.
        destruct H18 as [[_ H18] _]. assumption. }
      assert (g:|:b = f:|:b) as H22. {
        rewrite <- H19. symmetry. apply Restrict.TowerProperty.
        apply SOC.ElemIsIncl; assumption. }
      rewrite H21, H22. apply H14. assumption.
    - apply Single.Charac in H20.
      assert (g!b = F!f) as H21. {
        apply (SFO.EvalCharac g (succ c)). 1: assumption.
        + apply Union2.Charac. right. rewrite H20. apply Single.IsIn.
        + rewrite H20, H15. apply Union2.Charac. right. apply Single.IsIn. }
      rewrite H21, H20, H19. reflexivity. }
  assert (K' g (succ c)) as H21. {
    rewrite H9. split.
    - apply Succ.IsOrdinal. assumption.
    - split; assumption. }
  assert (:(c, F!f): :< f) as H22. {
    apply H10. exists g. exists (succ c). split. 2: assumption.
    rewrite H15. apply Union2.Charac. right. apply Single.IsIn. }
  assert (c :< SRD.domain f) as H23. {
    apply SRD.Charac. exists F!f. assumption. }
  rewrite H4 in H23. apply NoElemLoop1 with c. assumption.
Qed.

(* The transfinite recursion class is a function class defined on the ordinals. *)
Proposition IsFunctionOn : forall (F:Class),
  CFO.FunctionOn (Recursion F) On.
Proof.
  intros F. split.
  - apply IsFunction.
  - apply DomainIsOn.
Qed.

Lemma RestrictIsFunctionOn : forall (F:Class) (a:U), On a ->
  SFO.FunctionOn ((Recursion F) :|: a) a.
Proof.
  intros F a H1. split.
  - apply RestrictOfClass.IsFunction, IsFunction.
  - apply RestrictOfClass.DomainWhenIncl.
    + apply IsFunction.
    + apply Class.Incl.EquivCompatR with On.
      * apply Equiv.Sym, DomainIsOn.
      * intros x H2. apply SOC.IsOrdinal with a; assumption.
Qed.

Lemma K_Restrict : forall (F:Class) (f a:U),
  K F f a -> f = (Recursion F) :|: a.
Proof.
  intros F f a H1. assert (H2 := H1). destruct H2 as [H2 [H3 H4]].
  apply SFO.EqualCharac with a a. 1: assumption.
  - apply RestrictIsFunctionOn. assumption.
  - reflexivity.
  - intros x H5.
    assert (((Recursion F) :|: a)!x = (Recursion F)!x) as H6. {
      apply RestrictOfClass.Eval. 2: assumption. apply IsFunction. }
    rewrite H6. symmetry. apply (CFO.EvalCharac (Recursion F) On).
    + apply IsFunctionOn.
    + apply SOC.IsOrdinal with a; assumption.
    + apply Charac2. exists f. exists a. split. 2: assumption.
      apply SFO.Satisfies with a; assumption.
Qed.

(* The transfinite recursion class associated with F is F-recursive.            *)
Proposition IsRecursive : forall (F:Class) (b:U), On b ->
  (Recursion F)!b = F!((Recursion F) :|: b).
Proof.
  intros F b H1.
  assert (Recursion F :(b,(Recursion F)!b):) as H2. {
    apply CFO.Satisfies with On. 2: assumption. apply IsFunctionOn. }
  apply (proj1 (Charac2 _ _ _)) in H2. destruct H2 as [f [a [H2 H3]]].
  assert (H4 := H3). destruct H4 as [H4 [H5 H6]].
  assert (b :< a) as H7. {
    destruct H5 as [_ H5]. rewrite <- H5. apply SRD.Charac.
    exists (Recursion F)!b. assumption. }
  assert ((Recursion F)!b = f!b) as H8. {
    symmetry. apply (SFO.EvalCharac f a); assumption. }
  assert (f = (Recursion F) :|: a) as H9. { apply K_Restrict. assumption. }
  assert (f:|:b = (Recursion F) :|: b) as H10. {
    rewrite H9. apply RestrictOfClass.TowerProperty.
    - apply IsFunction.
    - apply SOC.ElemIsIncl; assumption. }
  rewrite H8, <- H10. apply H6. assumption.
Qed.

(* The transfinite recursion class is the unique F-recursive function on On.    *)
Proposition IsUnique : forall (F G:Class),
  CFO.FunctionOn G On                 ->
  (forall b, On b -> G!b = F!(G:|:b)) ->
  G :~: Recursion F.
Proof.
  intros F G H1 H2.
  apply (CFO.EqualCharac _ _ On On). 1: assumption.
  - apply IsFunctionOn.
  - split. 1: apply Equiv.Refl. apply Induction.Induction.
    intros a H3 H4.
    assert (SRD.domain (G:|:a) = a) as H6. {
      apply RestrictOfClass.DomainWhenIncl. 1: apply H1. destruct H1 as [_ H1].
      intros x H6. apply H1. apply SOC.IsOrdinal with a; assumption. }
    assert (SRD.domain ((Recursion F) :|: a) = a) as H7. {
      apply RestrictOfClass.DomainWhenIncl. 1: apply IsFunction.
      intros x H7. apply DomainIsOn. apply SOC.IsOrdinal with a; assumption. }
    assert (G:|:a = (Recursion F) :|: a) as H5. {
      apply SRF.EqualCharac.
      - apply RestrictOfClass.IsFunction, H1.
      - apply RestrictOfClass.IsFunction, IsFunction.
      - rewrite H6, H7. reflexivity.
      - intros x H8. rewrite H6 in H8.
        assert ((G:|:a)!x = G!x) as H9. {
          apply RestrictOfClass.Eval. 2: assumption. apply H1. }
        assert (((Recursion F) :|: a)!x = (Recursion F)!x) as H10. {
          apply RestrictOfClass.Eval. 2: assumption. apply IsFunction. }
        rewrite H9, H10. apply H4. assumption. }
    assert (G!a = F!(G:|:a)) as H8. { apply H2. assumption. }
    assert ((Recursion F)!a = F!((Recursion F) :|: a)) as H9. {
      apply IsRecursive. assumption. }
    rewrite H8, H9, H5. reflexivity.
Qed.

