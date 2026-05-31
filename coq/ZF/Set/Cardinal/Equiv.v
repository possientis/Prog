Require Import ZF.Axiom.Choice.
Require Import ZF.Axiom.Classic.
Require Import ZF.Class.DiffBySet.
Require Import ZF.Class.Equiv.
Require Import ZF.Class.Ordinal.FunctionOn.
Require Import ZF.Class.Ordinal.Recursion.
Require Import ZF.Class.Relation.FunctionOn.
Require Import ZF.Class.Relation.Fun.From.
Require Import ZF.Class.Small.
Require Import ZF.Set.Core.
Require Import ZF.Set.Diff.
Require Import ZF.Set.Empty.
Require Import ZF.Set.Foundation.
Require Import ZF.Set.Incl.
Require Import ZF.Set.Inter2.
Require Import ZF.Set.Order.Isom.
Require Import ZF.Set.Order.RestrictOfClass.
Require Import ZF.Set.Ordinal.Core.
Require Import ZF.Set.Ordinal.Limit.
Require Import ZF.Set.Ordinal.Mult.
Require Import ZF.Set.Ordinal.Mult2.
Require Import ZF.Set.Ordinal.Natural.
Require Import ZF.Set.Ordinal.Omega.
Require Import ZF.Set.Ordinal.Order.
Require Import ZF.Set.Ordinal.Order.E.
Require Import ZF.Set.Ordinal.Plus.
Require Import ZF.Set.Ordinal.Plus2.
Require Import ZF.Set.Ordinal.RecursionNOfClass.
Require Import ZF.Set.Ordinal.Succ.
Require Import ZF.Set.OrdPair.
Require Import ZF.Set.Power.
Require Import ZF.Set.Prod.
Require Import ZF.Set.Sum.
Require Import ZF.Set.Relation.Bij.
Require Import ZF.Set.Relation.Bijection.
Require Import ZF.Set.Relation.BijectionOn.
Require Import ZF.Set.Relation.Compose.
Require Import ZF.Set.Relation.Converse.
Require Import ZF.Set.Relation.Domain.
Require Import ZF.Set.Relation.Eval.
Require Import ZF.Set.Relation.Fun.
Require Import ZF.Set.Relation.Function.
Require Import ZF.Set.Relation.FunctionOn.
Require Import ZF.Set.Relation.Id.
Require Import ZF.Set.Relation.ImageUnderClass.
Require Import ZF.Set.Relation.Inj.
Require Import ZF.Set.Relation.Map.Sum.
Require Import ZF.Set.Relation.OneToOne.
Require Import ZF.Set.Relation.Range.
Require Import ZF.Set.Relation.RestrictOfClass.
Require Import ZF.Set.Relation.Fun.From.
Require Import ZF.Set.Relation.Fun.From2.
Require Import ZF.Set.Relation.Fun.IfThenElse.
Require Import ZF.Set.Single.
Require Import ZF.Set.Specify.
Require Import ZF.Set.Union2.

Require Import ZF.Notation.Equiv.
Export ZF.Notation.Equiv.

Module CEQ := ZF.Class.Equiv.
Module CFO := ZF.Class.Relation.FunctionOn.
Module COF := ZF.Class.Ordinal.FunctionOn.
Module CFF := ZF.Class.Relation.Fun.From.
Module SOO := ZF.Set.Ordinal.Order.
Module SOR := ZF.Set.Ordinal.RecursionNOfClass.
Module SRR := ZF.Set.Relation.RestrictOfClass.
Module SMS := ZF.Set.Relation.Map.Sum.

Definition equiv (a b:U) : Prop := exists f, Bij f a b.

(* Notation "a :~: b" := (equiv a b)                                            *)
Global Instance Equiv : Equiv U := { equiv := equiv }.

(* A set is well-orderable iff it is equipotent to some ordinal.                *)
Definition WellOrderable (a:U) : Prop := exists (b:U), Ordinal b /\ a :~: b.

(* Every set is equipotent to itself.                                           *)
Proposition Refl : forall (a:U), a :~: a.
Proof.
  intros a. exists (id a). apply Id.IsBij.
Qed.

(* Equipotence is symmetric.                                                    *)
Proposition Sym : forall (a b:U), a :~: b -> b :~: a.
Proof.
  intros a b [f H1]. exists f^:-1:. apply Bij.Converse. assumption.
Qed.

(* Equipotence is transitive.                                                   *)
Proposition Tran : forall (a b c:U), a :~: b -> b :~: c -> a :~: c.
Proof.
  intros a b c [f H1] [g H2]. exists (g :.: f).
  apply Bij.Compose with b; assumption.
Qed.

(* Assuming choice, every set is well-orderable.                                *)
Proposition IsWellOrderable : Choice ->
  forall (a:U), WellOrderable a.
Proof.
  intros AC a. specialize (AC :P(a)). destruct AC as [f [H1 H2]].
  remember (fun x => f!(a :\: range x)) as G eqn:H3.
  remember (Recursion (CFF.from G)) as F eqn:H4.
  assert (forall x,
    a :\: range x <> :0: -> f!(a :\: range x) :< a :\: range x) as H5. {
      intros x H5. apply H2. 2: assumption.
      apply Power.Charac, Diff.IsIncl. }
  assert (forall b, Ordinal b -> F!b = :[G]:!(F:|:b)) as H6. {
    intros b H6. rewrite H4. apply Recursion.IsRecursive. assumption. }
  assert (forall b , Ordinal b ->
    a :\: range (F:|:b) <> :0: -> F!b :< a :\: range (F:|:b)) as H7. {
      intros b H7 H8. rewrite H6, CFF.Eval, H3. 2: assumption.
      apply H5. assumption. }
  assert (CFO.FunctionOn F Ordinal) as G1. {
    rewrite H4. apply Recursion.IsFunctionOn. }
  assert (Small (toClass a)) as G2. { apply Small.SetIsSmall. }
  assert (CRD.domain F :~: Ordinal) as G3. { apply G1. }
  assert (forall b, Ordinal b               ->
    (toClass a :\: F:[b]:) :<>: :0: ->
    (toClass a :\: F:[b]:) F!b) as H8. {
      intros b H8 H9.
      assert (range (F:|:b) = F:[b]:) as H10. {
        apply RestrictOfClass.RangeOf, G1. }
      apply Diff.ToClass. rewrite <- H10. apply H7. 1: assumption.
      intros H11. apply H9.
      apply CEQ.Tran with (toClass (a :\: range (F:|:b))).
      - apply CEQ.Sym. rewrite <- H10. apply Diff.ToClass.
      - apply Empty.EmptyToClass. assumption. }
  assert (exists b,
    Ordinal b                                                     /\
    (forall c, c :< b -> (toClass a :\: F:[c]:) :<>: :0:) /\
    toClass F:[b]: :~: toClass a                                  /\
    SRO.OneToOne (F:|:b)) as H9. { apply COF.WhenFreshAndSmall; assumption. }
  destruct H9 as [b [H9 [H10 [H11 H12]]]].
  assert (F:[b]: = a) as H13. { apply CEQ.EqualToClass. assumption. }
  assert (range (F:|:b) = a) as H14. {
    rewrite <- H13. apply RestrictOfClass.RangeOf, G1. }
  assert (domain (F:|:b) = b) as H15. {
    apply RestrictOfClass.DomainWhenIncl.
    - apply G1.
    - intros c H15. apply G3. apply SOC.IsOrdinal with b; assumption. }
  assert (Bij (F:|:b) b a) as H16. {
    split. 2: assumption. split. 2: assumption. split. 2: assumption.
    apply SRR.IsRelation, G1. }
  exists b. split. 1: assumption. apply Sym. exists (F:|:b). assumption.
Qed.

(* A subset of an ordinal is equipotent to some ordinal within it.              *)
Proposition OrdinalSubset : forall (a b:U), Ordinal b ->
  a :<=: b  -> exists c, Ordinal c /\ c :<=: b /\ a :~: c.
Proof.
  intros a b H1 H2.
  assert (exists c f,
    Ordinal c /\ c :<=: b /\ Isom f (E c) (E a) c a) as H3. {
      apply SOO.OrdinalSubset; assumption. }
  destruct H3 as [c [f [H3 [H4 H5]]]].
  exists c.
  assert (a :~: c) as H6. { apply Sym. exists f. apply H5. }
  split. 1: assumption. split; assumption.
Qed.

(* Cantor-Schroeder-Bernstein: mutual injectability implies equipotence.        *)
Proposition CantorShroderBernstein : forall (a b c d:U),
  a :~: c   ->
  b :~: d   ->
  c :<=: b  ->
  d :<=: a  ->
  a :~: b.
Proof.
  intros a b c d H1 H2 H3 H4.
  destruct H1 as [f H1]. destruct H2 as [g H2].
  assert (range f = c) as G1. { apply H1. }
  assert (range g = d) as G2. { apply H2. }
  assert (domain f = a) as G3. { apply H1. }
  assert (domain g = b) as G4. { apply H2. }
  remember (fun x => (g :.: f) :[x]:) as H eqn:H5.
  remember (SOR.recursion (CFF.from H) (a :\: d)) as h eqn:H6.
  assert (FunctionOn h :N) as H7. { rewrite H6. apply SOR.IsFunctionOn. }
  assert (h!:0: = a :\: d) as H8. { rewrite H6. apply SOR.WhenZero. }
  assert (forall n, n :< :N -> h!(succ n) = (g :.: f) :[h!n]:) as H9. {
    intros n H9. rewrite H6, SOR.WhenSucc, <- H6, CFF.Eval, H5.
    2: assumption. reflexivity. }
  assert (Inj f a b) as H10. {
    split.
    - apply H1.
    - rewrite G1. assumption. }
  assert (Inj g b a) as H11. {
    split.
    - apply H2.
    - rewrite G2. assumption. }
  assert (Inj (g :.: f) a a) as H12. { apply Inj.Compose with b; assumption. }
  assert (forall n, n :< :N -> h!n :<=: a) as H13. {
    apply Omega.Induction.
    - rewrite H8. apply Diff.IsIncl.
    - intros n H13 IH. rewrite (H9 n). 2: assumption.
      intros y H14. apply Image.Charac in H14. destruct H14 as [x [H14 H15]].
      assert ((g :.: f)!x = y) as H16. {
        apply (Inj.Eval (g :.: f) a a); assumption. }
      rewrite <- H16. apply Inj.IsInRange with a. 1: assumption.
      apply IH. assumption. }
  assert (forall n, n :< :N -> f:[h!n]: :<=: b) as H14. {
    intros n H14 y H15. apply Image.Charac in H15. destruct H15 as [x [H15 H16]].
    assert (f!x = y) as H17. { apply (Bij.Eval f a c); assumption. }
    apply H3. rewrite <- H17. apply Bij.IsInRange with a. 1: assumption.
    apply (H13 n); assumption. }
  remember (fun x => exists n, n :< :N /\ x :< h!n) as A eqn:H15.
  remember (ifThenElse a A (fun x => f!x) (fun x => g^:-1:!x)) as k eqn:H16.
  assert (forall x n, ~ A x -> n :< :N -> ~ x :< h!n) as H17. {
    rewrite H15.
    intros x n H17 H18 H19. apply H17. exists n; split; assumption. }
  assert (FunctionOn k a) as H18. { rewrite H16. apply IfThenElse.IsFunctionOn. }
  assert (Bij g^:-1: d b) as H19. { apply Bij.Converse. assumption. }
  assert (domain g^:-1: = d) as H20. { apply H19. }
  assert (range g^:-1: = b) as H21. { apply H19. }
  assert (forall x, x :< a -> ~ A x -> x :< d) as H22. {
    intros x H22 H23.
    assert (~ x :< a :\: d) as H24. {
      rewrite <- H8. apply (H17 x :0:) in H23. 1: assumption.
      apply Omega.HasZero. }
    apply Classic.DoubleNegation. intros H25. apply H24.
    apply Diff.Charac. split; assumption. }
  assert (range k :<=: b) as H23. {
    intros y H23. apply (FunctionOn.RangeCharac k a) in H23. 2: assumption.
    destruct H23 as [x [H23 H24]]. rewrite <- H24.
    assert (A x \/ ~ A x) as H25. { apply LawExcludedMiddle. }
    destruct H25 as [H25|H25].
    - rewrite H16, IfThenElse.Eval1; try assumption.
      apply H3, Bij.IsInRange with a; assumption.
    - rewrite H16, IfThenElse.Eval2; try assumption.
      apply Bij.IsInRange with d. 1: assumption. apply H22; assumption. }
  assert (Fun k a b) as H24. { split; assumption. }
  assert (b :<=: range k) as H25. {
    intros y H25. apply (Fun.RangeCharac k a b). 1: assumption.
    remember (fun y => exists n, n :< :N /\ y :< f:[h!n]:) as B eqn:H26.
    assert (B y \/ ~ B y) as H27. { apply LawExcludedMiddle. }
    destruct H27 as [H27|H27]; rewrite H26 in H27.
    - destruct H27 as [n [H27 H28]].
      apply (Bij.ImageCharac f a c) in H28. 2: assumption.
      destruct H28 as [x [H28 [H29 H30]]].
      assert (k!x = y) as H31. {
        rewrite H16, IfThenElse.Eval1; try assumption.
        rewrite H15. exists n. split; assumption. }
      exists x. split; assumption.
    - assert (forall n, n :< :N -> ~ g!y :< h!n) as H28. {
        intros n H28 H29.
        assert (g!y :< d) as H30. { apply (Bij.IsInRange g b d); assumption. }
        assert (:0: :< n) as H31. {
          apply Omega.WhenNotZero. 1: assumption. intros H31.
          rewrite H31, H8 in H29. apply Diff.Charac in H29.
          destruct H29 as [H29 H32]. contradiction. }
        apply Omega.HasPred in H31. 2: assumption. destruct H31 as [m [H31 H32]].
        assert (h!(succ m) = g:[f:[h!m]:]:) as H33. {
          rewrite H9, Compose.Image. 2: assumption. reflexivity. }
        rewrite H32, H33 in H29.
        assert (y :< f:[h!m]:) as H34. {
          apply OneToOne.FromImage with g. 3: assumption.
          - apply H2.
          - rewrite G4. assumption. }
        apply H27. exists m. split; assumption. }
      assert (~ A g!y) as H29. {
        rewrite H15. intros [n [H29 H30]]. apply (H28 n); assumption. }
      assert (g!y :< a) as H30. { apply H4, (Bij.IsInRange g b d); assumption. }
      assert (k!(g!y) = g^:-1:!(g!y)) as H31. {
        rewrite H16, IfThenElse.Eval2; try assumption. reflexivity. }
      rewrite (Bij.ConverseEvalOfEval g b d) in H31; try assumption.
      exists g!y. split; assumption. }
  assert (range k = b) as H26. {
    apply Incl.Double. split; assumption. }
  assert (domain k = a) as G5. { apply H24. }
  assert (forall x y, x :< a -> y :< a -> k!x = k!y -> A x -> A y) as H27. {
    intros x y H27 H28 H29 H30. apply Classic.DoubleNegation. intros H31.
    assert (k!x = f!x) as H32. {
      rewrite H16, IfThenElse.Eval1; try assumption. reflexivity. }
    assert(k!y = g^:-1:!y) as H33. {
      rewrite H16, IfThenElse.Eval2; try assumption. reflexivity. }
    rewrite H32, H33 in H29.
    assert (Function f) as G6. { apply (Bij.IsFun f a c). assumption. }
    assert (Function g) as G7. { apply (Bij.IsFun g b d). assumption. }
    assert ((g :.: f)!x = y) as H34. {
      rewrite Function.ComposeEval, H29, (Bij.EvalOfConverseEval g b d);
      try assumption. 1: reflexivity.
      - apply H22; assumption.
      - rewrite G3. assumption.
      - rewrite G4, H29. apply Bij.IsInRange with d. 1: assumption.
        apply H22; assumption. }
    rewrite H15 in H30. destruct H30 as [n [H30 H35]].
    assert (succ n :< :N) as G8. { apply Omega.HasSucc. assumption. }
    assert (y :< h!(succ n)) as H36. {
      rewrite H9. 2: assumption. apply Image.Charac. exists x.
      split. 1: assumption. rewrite <- H34.
      apply Function.Satisfies.
      - apply Function.Compose; assumption.
      - apply Function.DomainOfCompose. 1: assumption. split.
        + rewrite G3. assumption.
        + rewrite G4. apply H3. apply (Bij.IsInRange f a c); assumption. }
    apply (H17 y (succ n)); assumption. }
  assert (OneToOne k) as H28. {
    apply FunctionOn.IsOneToOne with a. 1: assumption.
    intros x y H28 H29 H30.
    assert (A x \/ ~ A x) as H31. { apply LawExcludedMiddle. }
    destruct H31 as [H31|H31].
    - assert (A y) as H32. { apply H27 with x; assumption. }
      assert (k!x = f!x) as H33. {
        rewrite H16, IfThenElse.Eval1; try assumption. reflexivity. }
      assert (k!y = f!y) as H34. {
        rewrite H16, IfThenElse.Eval1; try assumption. reflexivity. }
      rewrite H33, H34 in H30.
      apply (Bij.EvalInjective f a c); assumption.
    - assert (~ A y) as H32. {
        intros H32.
        assert (A x) as H33. {
          apply H27 with y; try assumption. symmetry. assumption. }
        contradiction. }
      assert (k!x = g^:-1:!x) as H33. {
        rewrite H16, IfThenElse.Eval2; try assumption. reflexivity. }
      assert (k!y = g^:-1:!y) as H34. {
        rewrite H16, IfThenElse.Eval2; try assumption. reflexivity. }
      rewrite H33, H34 in H30.
      apply (Bij.EvalInjective g^:-1: d b); try assumption.
      + apply H22; assumption.
      + apply H22; assumption. }
  assert (Bijection k) as H29. {
    split. 2: assumption. apply H18. }
  assert (BijectionOn k a) as H30. { split; assumption. }
  assert (Bij k a b) as H31. { split; assumption. }
  exists k. assumption.
Qed.

(* Equipotent sets have equipotent power sets.                                  *)
Proposition PowerCompat : forall (a b:U),
  a :~: b -> :P(a) :~: :P(b).
Proof.
  intros a b [f H1].
  assert (Fun f a b) as G1. { apply Bij.IsFun. assumption. }
  assert (domain f = a) as G2. { apply H1. }
  assert (Bij f^:-1: b a) as G3. { apply Bij.Converse. assumption. }
  remember (from :P(a) (fun x => f:[x]:)) as g eqn:H2.
  assert (FunctionOn g :P(a)) as H3. { rewrite H2. apply From.IsFunctionOn. }
  assert (range g :<=: :P(b)) as H4. {
    intros y H4.
    apply (FunctionOn.RangeCharac g :P(a)) in H4. 2: assumption.
    destruct H4 as [x [H4 H5]]. rewrite H2, From.Eval in H5. 2: assumption.
    rewrite <- H5. apply Power.Charac. clear H5 y. intros y H5.
    apply Image.Charac in H5. destruct H5 as [u [H5 H6]].
    assert (f!u = y) as H7. {
      apply FunctionOn.Eval with a. 2: assumption. apply G1. }
    rewrite <- H7.
    assert (u :< a) as H8. {
      apply Power.Charac in H4. apply H4. assumption. }
    apply (Bij.IsInRange f a b); assumption. }
  assert (Fun g :P(a) :P(b)) as H9. { split; assumption. }
  assert (forall x y z,
    x :<=: a -> y :<=: a -> f:[x]: = f:[y]: -> z :< x -> z :< y) as H10. {
      intros x y z H10 H11 H12 H13.
    assert (f!z :< f:[x]:) as H14. {
      apply (Bij.ImageCharac f a b). 1: assumption.
      exists z. split. 1: assumption. split. 2: reflexivity.
      apply H10. assumption. }
    assert (f!z :< f:[y]:) as H15. { rewrite H12 in H14. assumption. }
    apply OneToOne.FromImage with f. 3: assumption.
    - apply H1.
    - rewrite G2. apply H10. assumption. }
  assert (OneToOne g) as H11. {
      apply (Fun.IsOneToOne g :P(a) :P(b)). 1: assumption.
      intros x y H11 H12 H13.
      rewrite H2, From.Eval, From.Eval in H13; try assumption.
      apply Power.Charac in H11. apply Power.Charac in H12.
      apply Incl.Double. split; intros z H14.
      - apply H10 with x; assumption.
      - apply H10 with y; try assumption. symmetry. assumption. }
  assert (:P(b) :<=: range g) as H12. {
    intros y H12.
    remember (f^:-1::[y]:) as x eqn:H13.
    assert (x :< :P(a)) as H14. {
      apply Power.Charac. intros z H14. rewrite H13 in H14.
      apply (Bij.ImageCharac f^:-1: b a) in H14. 2: assumption.
      destruct H14 as [u [H14 [H15 H16]]]. rewrite <- H16.
      apply (Bij.IsInRange f^:-1: b a); assumption. }
    assert (g!x = f:[f^:-1::[y]:]:) as H15. {
      rewrite H2, From.Eval, <- H13. 2: assumption. reflexivity. }
    assert (g!x = y) as H16. {
      rewrite (Bij.ImageOfInvImage f a b) in H15; try assumption.
      apply Power.Charac in H12. assumption. }
      apply (Fun.RangeCharac g :P(a) :P(b)). 1: assumption.
      exists x. split; assumption. }
  assert (Bij g :P(a) :P(b)) as H13. { apply Bij.FromFun; assumption. }
  exists g. assumption.
Qed.

(* No set is equipotent to its power set.                                       *)
Proposition Cantor : forall (a:U), ~ a :~: :P(a).
Proof.
  intros a H1.
  destruct H1 as [f H1].
  remember {{ x :< a | fun x => ~ x :< f!x }} as b eqn:H2.
  assert (b :<=: a) as H3. { rewrite H2. apply Specify.IsInclL. }
  apply Power.Charac in H3.
  apply (Bij.RangeCharac f a :P(a)) in H3. 2: assumption.
  destruct H3 as [c [H3 H4]].
  assert (c :< b \/ ~ c :< b) as H5. { apply LawExcludedMiddle. }
  destruct H5 as [H5|H5]; assert (H6 := H5).
  - rewrite H2 in H5. apply Specify.IsInclR in H5.
    rewrite H4 in H5. contradiction.
  - rewrite <- H4 in H5.
    assert (c :< b) as H7. {
      rewrite H2. apply Specify.Charac. split; assumption. }
    contradiction.
Qed.

(* A set is equipotent to the empty set if and only if it is empty.             *)
Proposition WhenZero : forall (a:U),
  a :~: :0: <-> a = :0:.
Proof.
  intros a. split; intros H1.
  - destruct H1 as [f H1]. apply Incl.Double. split; intros x H2.
    + exfalso.
      assert (f!x :< :0:) as H3. { apply (Bij.IsInRange f a :0:); assumption. }
      apply Empty.Charac in H3. contradiction.
    + apply Empty.Charac in H2. contradiction.
  - subst. apply Refl.
Qed.

(* Any singleton is equipotent to 1.                                            *)
Proposition WhenSingle : forall (a:U),
  :{a}: :~: :1:.
Proof.
  (* Proof by Claude + sonnet 4.6                                               *)
  (* The function sending a to 0 bijects {a} onto {0} = 1.                      *)
  intros a.
  remember (from :{a}: (fun _ => :0:)) as h eqn:Hh.
  assert (FunctionOn h :{a}:) as H1. { rewrite Hh. apply From.IsFunctionOn. }
  (* By definition, h(a) = 0.                                                   *)
  assert (h!a = :0:) as G1. {
    rewrite Hh. apply From.Eval. apply Single.IsIn. }
  (* range h <= 1 = {0}: h always returns 0, and 0 in {0}.                      *)
  assert (range h :<=: :1:) as H2. {
    intros y Hy.
    apply (FunctionOn.RangeCharac h :{a}:) in Hy. 2: assumption.
    destruct Hy as [x [Hx Hxy]].
    apply Single.Charac in Hx. subst x.
    rewrite <- Hxy, G1, Natural.OneExtension. apply Single.IsIn. }
  assert (Fun h :{a}: :1:) as H3. { split; assumption. }
  (* Surjectivity: the unique element 0 of 1 = {0} has preimage a.              *)
  assert (:1: :<=: range h) as H4. {
    intros y Hy.
    rewrite Natural.OneExtension in Hy. apply Single.Charac in Hy. subst y.
    apply (FunctionOn.RangeCharac h :{a}:). 1: assumption.
    exists a. split. 1: apply Single.IsIn. exact G1. }
  (* Injectivity: {a} has only one element, so any two elements are equal.      *)
  assert (OneToOne h) as H5. {
    apply (FunctionOn.IsOneToOne h :{a}:). 1: assumption.
    intros x y Hx Hy _.
    apply Single.Charac in Hx. apply Single.Charac in Hy.
    rewrite Hx, Hy. reflexivity. }
  exists h. apply Bij.FromFun; assumption.
Qed.

(* Adding b to a gives either a itself or a set equipotent to succ(a).          *)
Proposition AddElem : forall (a b:U),
  a :\/: :{b}: = a \/ a :\/: :{b}: :~: succ a.
Proof.
  intros a b.
  assert (b :< a \/ ~ b :< a) as H1. { apply LawExcludedMiddle. }
  destruct H1 as [H1|H1].
  - assert (a :\/: :{b}: = a) as H2. {
      apply Incl.Double. split. 2: apply Union2.IsInclL.
      intros x H2.
      apply Union2.Charac in H2. destruct H2 as [H2|H2]. 1: assumption.
      apply Single.Charac in H2. subst. assumption. }
    left. assumption.
  - assert (a :\/: :{b}: :~: succ a) as H2. {
      remember (fun x => x = b) as A eqn:H2.
      remember (ifThenElse (a :\/: :{b}:) A (fun x => a) (fun x => x)) as f eqn:H3.
      assert (FunctionOn f (a :\/: :{b}:)) as H4. {
        rewrite H3. apply IfThenElse.IsFunctionOn. }
      assert (forall x, x :< a -> f!x = x) as G1. {
        intros x G1. rewrite H3, IfThenElse.Eval2. 1: reflexivity.
        - apply Union2.Charac. left. assumption.
        - rewrite H2. intros G2. subst. contradiction. }
      assert (forall x, x = b -> f!x = a) as G2. {
        intros x G2. rewrite H3, IfThenElse.Eval1. 1: reflexivity.
        - apply Union2.Charac. right. rewrite G2. apply Single.IsIn.
        - rewrite H2. assumption. }
      assert (range f :<=: succ a) as H5. {
        intros y H5. apply (FunctionOn.RangeCharac f (a :\/: :{b}:)) in H5.
        2: assumption. destruct H5 as [x [H5 H6]].
        apply Union2.Charac in H5. destruct H5 as [H5|H5].
        - assert (f!x = x) as H7. { apply G1. assumption. }
          rewrite <- H6, H7. apply Union2.Charac. left. assumption.
        - apply Single.Charac in H5.
          assert (f!x = a) as H7. { apply G2. assumption. }
          rewrite <- H6, H7. apply Union2.Charac. right. apply Single.IsIn. }
      assert (Fun f (a :\/: :{b}:) (succ a)) as H6. { split; assumption. }
      assert (succ a :<=: range f) as H7. {
        intros y H7.
        apply Union2.Charac in H7. destruct H7 as [H7|H7].
        - assert (f!y = y) as H8. { apply G1. assumption. }
          apply (FunctionOn.RangeCharac f (a :\/: :{b}:)). 1: assumption.
          exists y. split. 2: assumption.
          apply Union2.Charac. left. assumption.
        - apply Single.Charac in H7.
          assert (f!b = a) as H8. { apply G2. reflexivity. }
          apply (FunctionOn.RangeCharac f (a :\/: :{b}:)). 1: assumption.
          exists b. split.
          + apply Union2.Charac. right. apply Single.IsIn.
          + rewrite H7. assumption. }
      assert (OneToOne f) as H8. {
        apply (Fun.IsOneToOne f (a :\/: :{b}:) (succ a)). 1: assumption.
          intros x y H8 H9 H10.
          apply Union2.Charac in H8. apply Union2.Charac in H9.
          destruct H8 as [H8|H8]; destruct H9 as [H9|H9].
          - assert (f!x = x) as H11. { apply G1. assumption. }
            assert (f!y = y) as H12. { apply G1. assumption. }
            rewrite <- H11, <- H12. assumption.
          - exfalso. apply Single.Charac in H9.
            assert (f!x = x) as H11. { apply G1. assumption. }
            assert (f!y = a) as H12. { apply G2. assumption. }
            rewrite <- H11, H10, H12 in H8. revert H8.
            apply Foundation.NoLoop1.
          - exfalso. apply Single.Charac in H8.
            assert (f!x = a) as H11. { apply G2. assumption. }
            assert (f!y = y) as H12. { apply G1. assumption. }
            rewrite <- H12, <- H10, H11 in H9. revert H9.
            apply Foundation.NoLoop1.
          - apply Single.Charac in H8. apply Single.Charac in H9.
            rewrite H8, H9. reflexivity. }
      assert (Bij f (a :\/: :{b}:) (succ a)) as H9. {
        apply Bij.FromFun; assumption. }
      exists f. assumption. }
    right. assumption.
Qed.

(* The product {b} x a of a singleton and a set a is equipotent to a.           *)
Proposition ProdSingleL : forall (a b:U), :{b}: :x: a :~: a.
Proof.
  intros a b.
  assert (a :~: :{b}: :x: a) as H1. {
    remember (from a (fun x => :(b,x):)) as f eqn:H1.
    assert (FunctionOn f a) as H2. { rewrite H1. apply From.IsFunctionOn. }
    assert (forall x, x :< a -> f!x = :(b,x):) as G1. {
      intros x G1. rewrite H1, From.Eval. 2: assumption. reflexivity. }
    assert (range f :<=: :{b}: :x: a) as H3. {
      intros y H3.
      apply (FunctionOn.RangeCharac f a) in H3. 2: assumption.
      destruct H3 as [x [H3 H4]].
      rewrite <- H4, (G1 x). 2: assumption. apply Prod.Charac2.
      split. 2: assumption. apply Single.IsIn. }
    assert (Fun f a (:{b}: :x: a)) as H4. { split; assumption. }
    assert (:{b}: :x: a :<=: range f) as H5. {
      intros y H5. apply Prod.Charac in H5. destruct H5 as [u [x [H5 [H6 H7]]]].
      apply Single.Charac in H6. rewrite H6 in H5.
      assert (f!x = y) as H8. { rewrite H5. apply G1. assumption. }
      apply (FunctionOn.RangeCharac f a). 1: assumption.
      exists x. split; assumption. }
    assert (OneToOne f) as H6. {
      apply (FunctionOn.IsOneToOne f a). 1: assumption.
      intros x y H6 H7 H8.
      rewrite (G1 x), (G1 y) in H8; try assumption.
      apply OrdPair.Equal in H8. apply H8. }
    assert (Bij f a (:{b}: :x: a)) as H7. { apply Bij.FromFun; assumption. }
    exists f. assumption. }
  apply Sym. assumption.
Qed.


(* Equipotence is compatible with cartesian products.                           *)
Proposition ProdCompat : forall (a b c d:U),
  a :~: c -> b :~: d -> a :x: b :~: c :x: d.
Proof.
  (* Proof by Claude + sonnet 4.6                                               *)
  (* Let f : a -> c and g : b -> d be the bijections given by the hypotheses.   *)
  intros a b c d [f H1] [g H2].
  (* Define h : a x b -> c x d by h(u,v) = (f(u), g(v)).                        *)
  remember (from2 a b (fun u v => :(f!u, g!v):)) as h eqn:Hh.
  assert (FunctionOn h (a :x: b)) as H3. { rewrite Hh. apply From2.IsFunctionOn. }
  (* By definition, for u in a and v in b, h(u,v) = (f(u), g(v)).               *)
  assert (forall u v, u :< a -> v :< b -> h!(:(u,v):) = :(f!u, g!v):) as G1. {
    intros u v Hu Hv. rewrite Hh. rewrite From2.Eval by assumption. reflexivity. }
  (* range h <= c x d: for each (u,v) in a x b, f(u) in c and g(v) in d,        *)
  (* so h(u,v) = (f(u), g(v)) lies in c x d.                                    *)
  assert (range h :<=: c :x: d) as H4. {
    intros y Hy.
    apply (FunctionOn.RangeCharac h (a :x: b)) in Hy. 2: assumption.
    destruct Hy as [p [Hp Hpy]].
    apply Prod.Charac in Hp. destruct Hp as [u [v [Hp [Hu Hv]]]].
    rewrite <- Hpy, Hp, (G1 u v Hu Hv).
    apply Prod.Charac2. split.
    - exact (Bij.IsInRange f a c u H1 Hu).
    - exact (Bij.IsInRange g b d v H2 Hv). }
  assert (Fun h (a :x: b) (c :x: d)) as H5. { split; assumption. }
  (* Surjectivity: for (c1,d1) in c x d, find u in a with f(u) = c1 and         *)
  (* v in b with g(v) = d1 (by surjectivity of f and g); then h(u,v) = (c1,d1). *)
  assert (c :x: d :<=: range h) as H6. {
    intros z Hz.
    apply Prod.Charac in Hz. destruct Hz as [c1 [d1 [Hz [Hc1 Hd1]]]].
    apply (Bij.RangeCharac f a c c1 H1) in Hc1. destruct Hc1 as [u [Hu Hfu]].
    apply (Bij.RangeCharac g b d d1 H2) in Hd1. destruct Hd1 as [v [Hv Hgv]].
    apply (FunctionOn.RangeCharac h (a :x: b)). 1: assumption.
    exists :(u,v):. split.
    - apply Prod.Charac2. split; assumption.
    - rewrite (G1 u v Hu Hv), Hfu, Hgv. symmetry. exact Hz. }
  (* Injectivity: h(u1,v1) = h(u2,v2) gives (f(u1),g(v1)) = (f(u2),g(v2)),      *)
  (* hence u1 = u2 and v1 = v2 by injectivity of f and g respectively.          *)
  assert (OneToOne h) as H7. {
    apply (FunctionOn.IsOneToOne h (a :x: b)). 1: assumption.
    intros p q Hp Hq Hpq.
    apply Prod.Charac in Hp. destruct Hp as [u1 [v1 [Hp [Hu1 Hv1]]]].
    apply Prod.Charac in Hq. destruct Hq as [u2 [v2 [Hq [Hu2 Hv2]]]].
    rewrite Hp, Hq, (G1 u1 v1 Hu1 Hv1), (G1 u2 v2 Hu2 Hv2) in Hpq.
    apply OrdPair.Equal in Hpq. destruct Hpq as [Hf Hg].
    apply (Bij.EvalInjective f a c u1 u2 H1 Hu1 Hu2) in Hf.
    apply (Bij.EvalInjective g b d v1 v2 H2 Hv1 Hv2) in Hg.
    rewrite Hp, Hq, Hf, Hg. reflexivity. }
  exists h. apply Bij.FromFun; assumption.
Qed.

(* Equipotence is left-compatible with cartesian product.                       *)
Proposition ProdCompatL : forall (a b c:U),
  a :~: b -> a :x: c :~: b :x: c.
Proof.
  (* Proof by Claude + sonnet 4.6                                               *)
  (* If a ~ b then a x c ~ b x c.                                               *)
  intros a b c H.
  exact (ProdCompat a c b c H (Refl c)).
Qed.

(* Equipotence is right-compatible with cartesian product.                      *)
Proposition ProdCompatR : forall (a b c:U),
  a :~: b -> c :x: a :~: c :x: b.
Proof.
  (* Proof by Claude + sonnet 4.6                                               *)
  (* If a ~ b then c x a ~ c x b.                                               *)
  intros a b c H.
  exact (ProdCompat c a c b (Refl c) H).
Qed.

(* The cartesian product of two well-orderable sets is well-orderable.          *)
Proposition WellOrderableProd : forall (a b:U),
  WellOrderable a -> WellOrderable b -> WellOrderable (a :x: b).
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros a b [c [H1 H2]] [d [H3 H4]].
  (* Replace both factors by ordinals, preserving the cartesian product.        *)
  assert (a :x: b :~: c :x: d) as H5. { apply ProdCompat; assumption. }
  (* The ordinal product orders d x c as the ordinal d*c.                       *)
  assert (c :x: d :~: d :*: c) as H6. {
    exists (Mult2.f d c). apply Mult2.IsBij; assumption. }
  (* Transporting the bijections gives an ordinal representative.               *)
  exists (d :*: c). split.
  - apply Mult.IsOrdinal; assumption.
  - apply Tran with (c :x: d); assumption.
Qed.


(* Equipotence is compatible with disjoint sums.                                *)
Proposition SumCompat : forall (a b c d:U),
  a :~: c -> b :~: d -> a :++: b :~: c :++: d.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros a b c d [f H1] [g H2].
  remember ((inL c d) :.: f) as f' eqn:H3.
  remember ((inR c d) :.: g) as g' eqn:H4.
  (* The induced either map is a bijection between the two disjoint sums.       *)
  exists (either a b f' g'). apply (SMS.IsBij a b c d f g); assumption.
Qed.

(* Equipotence is left-compatible with disjoint sums.                            *)
Proposition SumCompatL : forall (a b c:U),
  a :~: b -> a :++: c :~: b :++: c.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros a b c H1.
  (* Keep the right summand fixed and use the identity bijection there.         *)
  apply SumCompat. 1: assumption. apply Refl.
Qed.

(* Equipotence is right-compatible with disjoint sums.                           *)
Proposition SumCompatR : forall (a b c:U),
  a :~: b -> c :++: a :~: c :++: b.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros a b c H1.
  (* Keep the left summand fixed and use the identity bijection there.          *)
  apply SumCompat. 2: assumption. apply Refl.
Qed.

(* The disjoint sum of two well-orderable sets is well-orderable.                *)
Proposition WellOrderableSum : forall (a b:U),
  WellOrderable a -> WellOrderable b -> WellOrderable (a :++: b).
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  intros a b [c [H1 H2]] [d [H3 H4]].
  (* Replace both summands by ordinals, preserving the disjoint sum.            *)
  assert (a :++: b :~: c :++: d) as H5. { apply SumCompat; assumption. }
  (* The ordinal sum orders c ++ d as the ordinal c+d.                          *)
  assert (c :++: d :~: c :+: d) as H6. {
    exists (Plus2.f c d). apply Plus2.IsBij; assumption. }
  (* Transporting the bijections gives an ordinal representative.               *)
  exists (c :+: d). split.
  - apply Plus.IsOrdinal; assumption.
  - apply Tran with (c :++: d); assumption.
Qed.


(* Equipotence is compatible with the successor operation.                      *)
Proposition SuccCompat : forall (a b:U),
  a :~: b ->  succ a :~: succ b.
Proof.
  (* Proof by Claude + sonnet 4.6                                               *)
  (* Let f : a -> b be the bijection given by the hypothesis.                   *)
  intros a b [f H1].
  (* Define h : succ(a) -> succ(b) by h(a) = b and h(x) = f(x) for x in a.      *)
  remember (fun x => x = a) as A eqn:H2.
  remember (ifThenElse (succ a) A (fun _ => b) (fun x => f!x)) as h eqn:H3.
  assert (FunctionOn h (succ a)) as H4. {
    rewrite H3. apply IfThenElse.IsFunctionOn. }
  (* For x in a, x is not a by foundation, so h(x) = f(x).                      *)
  assert (forall x, x :< a -> h!x = f!x) as G1. {
    intros x G1. rewrite H3, IfThenElse.Eval2. 1: reflexivity.
    - apply Succ.Charac. right. assumption.
    - rewrite H2. intros G2. subst. revert G1. apply Foundation.NoLoop1. }
  (* h maps the new top element to the new top element: h(a) = b.               *)
  assert (h!a = b) as G2. {
    rewrite H3, IfThenElse.Eval1. 1: reflexivity.
    - apply Succ.IsIn.
    - rewrite H2. reflexivity. }
  (* range h <= succ(b): h(a) = b in succ(b); for x in a, h(x) = f(x) in b,     *)
  (* and b is a subset of succ(b).                                              *)
  assert (range h :<=: succ b) as H5. {
    intros y H5.
    apply (FunctionOn.RangeCharac h (succ a)) in H5. 2: assumption.
    destruct H5 as [x [H5 H6]].
    apply Succ.Charac in H5. destruct H5 as [H5|H5].
    - rewrite <- H6, H5, G2. apply Succ.IsIn.
    - rewrite <- H6, (G1 x H5). apply Succ.Charac. right.
      exact (Bij.IsInRange f a b x H1 H5). }
  assert (Fun h (succ a) (succ b)) as H6. { split; assumption. }
  (* Surjectivity: b in succ(b) has preimage a since h(a) = b; for y in b,      *)
  (* surjectivity of f gives x in a with f(x) = y, hence h(x) = y.              *)
  assert (succ b :<=: range h) as H7. {
    intros y H7. apply Succ.Charac in H7. destruct H7 as [H7|H7].
    - rewrite H7. apply (FunctionOn.RangeCharac h (succ a)). 1: assumption.
      exists a. split. 1: apply Succ.IsIn. exact G2.
    - apply (Bij.RangeCharac f a b y H1) in H7. destruct H7 as [x [Hx Hfx]].
      apply (FunctionOn.RangeCharac h (succ a)). 1: assumption.
      exists x. split.
      + apply Succ.Charac. right. assumption.
      + rewrite (G1 x Hx). assumption. }
  (* Injectivity: four cases. x = y = a is trivial. If x = a and y lies in a,   *)
  (* h(a) = b = f(y) in b gives b in b, contradicting the axiom of foundation.  *)
  (* Both in a: f(x) = f(y) and injectivity of f give x = y.                    *)
  assert (OneToOne h) as H8. {
    apply (Fun.IsOneToOne h (succ a) (succ b)). 1: assumption.
    intros x y H8 H9 H10.
    apply Succ.Charac in H8. apply Succ.Charac in H9.
    destruct H8 as [H8|H8]; destruct H9 as [H9|H9].
    - subst. reflexivity.
    - subst. exfalso.
      rewrite G2, (G1 y H9) in H10.
      assert (f!y :< b) as H11. { exact (Bij.IsInRange f a b y H1 H9). }
      rewrite <- H10 in H11. revert H11. apply Foundation.NoLoop1.
    - subst. exfalso.
      rewrite (G1 x H8), G2 in H10.
      assert (f!x :< b) as H11. { exact (Bij.IsInRange f a b x H1 H8). }
      rewrite H10 in H11. revert H11. apply Foundation.NoLoop1.
    - rewrite (G1 x H8), (G1 y H9) in H10.
      exact (Bij.EvalInjective f a b x y H1 H8 H9 H10). }
  exists h. apply Bij.FromFun; assumption.
Qed.

Proposition SuccCompatRev : forall (a b:U),
  succ a :~: succ b -> a :~: b.
Proof.
  (* Proof by Claude + sonnet 4.6                                               *)
  (* Let f : succ(a) -> succ(b) be the given bijection.                         *)
  intros a b [f H1].
  assert (a :< succ a) as G1. { apply Succ.IsIn. }
  assert (a :<=: succ a) as G2. { apply Succ.IsIncl. }
  assert (f!a :< succ b) as G3. {
    apply (Bij.IsInRange f (succ a) (succ b)); assumption. }
  (* For x in a define h(x) = f(a) if f(x) = b, else h(x) = f(x).               *)
  remember (ifThenElse a (fun x => f!x = b) (fun _ => f!a) (fun x => f!x))
    as h eqn:H2.
  assert (FunctionOn h a) as H3. { rewrite H2. apply IfThenElse.IsFunctionOn. }
  assert (forall x, x :< a -> f!x = b  -> h!x = f!a) as G4. {
    intros x H4 H5. rewrite H2, IfThenElse.Eval1. 1: reflexivity.
    all: assumption. }
  assert (forall x, x :< a -> f!x <> b -> h!x = f!x) as G5. {
    intros x H4 H5. rewrite H2, IfThenElse.Eval2. 1: reflexivity.
    all: assumption. }
  (* If f(x) = b for x in a, then f(a) is not b; otherwise x = a contradicts    *)
  (* foundation.                                                                *)
  assert (forall x, x :< a -> f!x = b -> f!a <> b) as G6. {
    intros x H4 H5 H6.
    assert (x = a) as H7. {
      apply (Bij.EvalInjective f (succ a) (succ b)).
      1: assumption. 1: apply G2, H4. 1: apply G1.
      rewrite H5. symmetry. assumption. }
    rewrite H7 in H4. revert H4. apply Foundation.NoLoop1. }
  (* h takes values in b: either h(x) = f(a), with f(a) in b because            *)
  (* f(a) is not b, or h(x) = f(x), with f(x) in b because f(x) is not b.       *)
  assert (range h :<=: b) as H4. {
    intros y H4.
    apply (FunctionOn.RangeCharac h a) in H4. 2: assumption.
    destruct H4 as [x [H4 H5]].
    assert (f!x = b \/ f!x <> b) as [H6|H6]. { apply LawExcludedMiddle. }
    - rewrite (G4 x H4 H6) in H5. rewrite <- H5.
      apply Succ.Charac in G3. destruct G3 as [G3|G3].
      + exfalso. apply (G6 x H4 H6). assumption.
      + assumption.
    - rewrite (G5 x H4 H6) in H5. rewrite <- H5.
      assert (f!x :< succ b) as H7. {
        apply (Bij.IsInRange f (succ a) (succ b)); try assumption.
        apply G2. assumption. }
      apply Succ.Charac in H7. destruct H7 as [H7|H7].
      + exfalso. apply H6. assumption.
      + assumption. }
  assert (Fun h a b) as H5. { split; assumption. }
  (* Surjectivity: for z in b, find x in a with h(x) = z.                       *)
  (* b is not in b by foundation, so z is not b.                                *)
  assert (b :<=: range h) as H6. {
    intros z H6.
    assert (z :< succ b) as H7. { apply Succ.Charac. right. assumption. }
    apply (Bij.RangeCharac f (succ a) (succ b)) in H7. 2: assumption.
    destruct H7 as [u [H7 H8]].
    apply Succ.Charac in H7. destruct H7 as [H7|H7].
    - (* u = a: f(a) = z. Surjectivity gives v with f(v) = b.                   *)
      subst u.
      assert (b :< succ b) as H9. { apply Succ.IsIn. }
      apply (Bij.RangeCharac f (succ a) (succ b)) in H9. 2: assumption.
      destruct H9 as [v [H9 H10]].
      apply Succ.Charac in H9. destruct H9 as [H9|H9].
      + (* v = a: f(a) = b = z, but z in b contradicts foundation.              *)
        subst v. rewrite H10 in H8.
        exfalso. rewrite <- H8 in H6. revert H6. apply Foundation.NoLoop1.
      + (* v in a: h(v) = f(a) = z.                                             *)
        apply (FunctionOn.RangeCharac h a). 1: assumption.
        exists v. split. 1: assumption.
        rewrite (G4 v H9 H10). assumption.
    - (* u lies in a: f(u) = z, and z is not b, so h(u) = f(u) = z.             *)
      apply (FunctionOn.RangeCharac h a). 1: assumption.
      exists u. split. 1: assumption.
      assert (f!u <> b) as H9. {
        intros H9.
        assert (z = b) as H10. { rewrite <- H8. assumption. }
        rewrite H10 in H6. revert H6. apply Foundation.NoLoop1. }
      rewrite (G5 u H7 H9). assumption. }
  (* Injectivity: four cases on whether f(x) = b and f(y) = b.                  *)
  assert (OneToOne h) as H7. {
    apply (Fun.IsOneToOne h a b). 1: assumption.
    intros x y H7 H8 H9.
    assert (f!x = b \/ f!x <> b) as [H10|H10]. { apply LawExcludedMiddle. }
    - assert (f!y = b \/ f!y <> b) as [H11|H11]. { apply LawExcludedMiddle. }
      + (* Both f(x) = b, f(y) = b: injectivity of f gives x = y.               *)
        apply (Bij.EvalInjective f (succ a) (succ b)).
        1: assumption. 1: apply G2, H7. 1: apply G2, H8.
        rewrite H10, H11. reflexivity.
      + (* f(x) = b, f(y) is not b: h(x) = f(a) = h(y) = f(y) gives a = y,      *)
        (* contradicting y in a.                                                *)
        exfalso.
        rewrite (G4 x H7 H10), (G5 y H8 H11) in H9.
        assert (a = y) as H12. {
          apply (Bij.EvalInjective f (succ a) (succ b)).
          1: assumption. 1: apply G1. 1: apply G2, H8. assumption. }
        rewrite <- H12 in H8. revert H8. apply Foundation.NoLoop1.
    - assert (f!y = b \/ f!y <> b) as [H11|H11]. { apply LawExcludedMiddle. }
      + (* f(x) is not b, f(y) = b: symmetric.                                  *)
        exfalso.
        rewrite (G5 x H7 H10), (G4 y H8 H11) in H9.
        assert (a = x) as H12. {
          apply (Bij.EvalInjective f (succ a) (succ b)).
          1: assumption. 1: apply G1. 1: apply G2, H7. symmetry. assumption. }
        rewrite <- H12 in H7. revert H7. apply Foundation.NoLoop1.
      + (* Both f(x) and f(y) are not b: h(x) = f(x) = f(y) = h(y).             *)
        rewrite (G5 x H7 H10), (G5 y H8 H11) in H9.
        apply (Bij.EvalInjective f (succ a) (succ b)).
        1: assumption. 1: apply G2, H7. 1: apply G2, H8. assumption. }
  exists h. apply Bij.FromFun; assumption.
Qed.

Proposition WellOrderableSucc : forall (a:U),
  WellOrderable a -> WellOrderable (succ a).
Proof.
  intros a [b [H1 H2]].
  assert (succ a :~: succ b) as H3. { apply SuccCompat. assumption. }
  assert (Ordinal (succ b)) as H4. { apply Succ.IsOrdinal. assumption. }
  exists (succ b). split; assumption.
Qed.

(* If a and b are disjoint, a ~ c and b ~ d, then a \/ b ~ c + d.               *)
Proposition DisjointUnion : forall (a b c d:U),
  Ordinal c               ->
  Ordinal d               ->
  a :~: c                 ->
  b :~: d                 ->
  a :/\: b  = :0:         ->
  a :\/: b  :~: c :+: d.
Proof.
  (* Proof by Claude + sonnet 4.6                                               *)
  (* Let f : a -> c and g : b -> d be the bijections given by the hypotheses.   *)
  intros a b c d Hc Hd [f Hf] [g Hg] Hdisj.
  (* Define h : a \/ b -> {0} x c \/ {1} x d by case on membership:             *)
  (*   h(x) = (0, f!x)  for x in a  (lands in {0} x c since f!x in c)           *)
  (*   h(x) = (1, g!x)  for x in b  (lands in {1} x d since g!x in d)           *)
  remember (ifThenElse (a :\/: b) (fun x => x :< a)
    (fun x => :( :0: , f!x ):) (fun x => :( :1: , g!x ):)) as h eqn:Hh.
  assert (FunctionOn h (a :\/: b)) as HFon. {
    rewrite Hh. apply IfThenElse.IsFunctionOn. }
  (* By definition, for any x in a, h!x = (0, f!x).                             *)
  assert (forall x, x :< a -> h!x = :( :0: , f!x ):) as HEvalA. {
    intros x Hx. rewrite Hh, IfThenElse.Eval1. 1: reflexivity.
    - apply Union2.IsInclL. assumption.
    - assumption. }
  (* Disjointness: a /\ b = 0 means x in b implies x not in a.                  *)
  assert (forall x, x :< b -> ~ x :< a) as HDisjAB. {
    intros x Hxb Hxa.
    assert (x :< a :/\: b) as H. { apply Inter2.Charac. split; assumption. }
    rewrite Hdisj in H. revert H. apply Empty.Charac. }
  (* By disjointness, for any x in b, h!x = (1, g!x).                           *)
  assert (forall x, x :< b -> h!x = :( :1: , g!x ):) as HEvalB. {
    intros x Hx. rewrite Hh, IfThenElse.Eval2. 1: reflexivity.
    - apply Union2.IsInclR. assumption.
    - apply HDisjAB. assumption. }
  (* range h <= {0} x c \/ {1} x d:                                             *)
  (*   a-side: h!x = (0, f!x) with f!x in c  =>  h!x in {0} x c.                *)
  (*   b-side: h!x = (1, g!x) with g!x in d  =>  h!x in {1} x d.                *)
  assert (range h :<=: sum c d) as HRangeIncl. {
    intros e He.
    apply (FunctionOn.RangeCharac h (a :\/: b)) in He. 2: assumption.
    destruct He as [x [Hx Hxe]].
    apply Union2.Charac in Hx. destruct Hx as [Hxa | Hxb].
    - rewrite HEvalA in Hxe. 2: assumption. subst e.
      unfold sum. apply Union2.IsInclL.
      apply Prod.Charac2. split. 1: apply Single.IsIn.
      apply Bij.IsInRange with a; assumption.
    - rewrite HEvalB in Hxe. 2: assumption. subst e.
      unfold sum. apply Union2.IsInclR.
      apply Prod.Charac2. split. 1: apply Single.IsIn.
      apply Bij.IsInRange with b; assumption. }
  assert (Fun h (a :\/: b) (sum c d)) as HFun. { split; assumption. }
  (* Surjectivity: {0} x c \/ {1} x d <= range h.                               *)
  (* Every element of {0} x c \/ {1} x d is (0,e') with e' in c, or             *)
  (* (1,e') with e' in d. Surjectivity of f (resp. g) supplies the preimage.    *)
  assert (sum c d :<=: range h) as HSurj. {
    intros p Hp. unfold sum in Hp.
    apply Union2.Charac in Hp. destruct Hp as [Hp | Hp].
    - (* p in {0} x c: p = (0,e') with e' in c.                                 *)
      apply Prod.Charac in Hp. destruct Hp as [t [e' [Hpeq [Ht He']]]].
      apply Single.Charac in Ht. subst t. subst p.
      apply (Bij.RangeCharac f a c e' Hf) in He'. destruct He' as [x [Hxa Hfx]].
      apply (FunctionOn.RangeCharac h (a :\/: b)). 1: assumption.
      exists x. split.
      + apply Union2.IsInclL. assumption.
      + rewrite (HEvalA x Hxa), Hfx. reflexivity.
    - (* p in {1} x d: p = (1,e') with e' in d.                                 *)
      apply Prod.Charac in Hp. destruct Hp as [t [e' [Hpeq [Ht He']]]].
      apply Single.Charac in Ht. subst t. subst p.
      apply (Bij.RangeCharac g b d e' Hg) in He'. destruct He' as [y [Hyb Hgy]].
      apply (FunctionOn.RangeCharac h (a :\/: b)). 1: assumption.
      exists y. split.
      + apply Union2.IsInclR. assumption.
      + rewrite (HEvalB y Hyb), Hgy. reflexivity. }
  (* Injectivity: h is one-to-one. Four cases on membership of x, y in a or b.  *)
  assert (OneToOne h) as HInj. {
    apply (Fun.IsOneToOne h (a :\/: b) (sum c d)). 1: assumption.
    intros x y Hx Hy Hxy.
    apply Union2.Charac in Hx. apply Union2.Charac in Hy.
    destruct Hx as [Hxa | Hxb]; destruct Hy as [Hya | Hyb].
    - (* x, y both in a: (0,f!x) = (0,f!y) => f!x = f!y, then f injective.      *)
      rewrite (HEvalA x Hxa), (HEvalA y Hya) in Hxy.
      apply OrdPair.Equal in Hxy. destruct Hxy as [_ Hfxy].
      exact (Bij.EvalInjective f a c x y Hf Hxa Hya Hfxy).
    - (* x in a, y in b: (0,f!x) = (1,g!y) => 0 = 1, a contradiction.           *)
      exfalso.
      rewrite (HEvalA x Hxa), (HEvalB y Hyb) in Hxy.
      apply OrdPair.Equal in Hxy. destruct Hxy as [H01 _].
      exact (Natural.ZeroIsNotOne H01).
    - (* x in b, y in a: (1,g!x) = (0,f!y) => 1 = 0, a contradiction.           *)
      exfalso.
      rewrite (HEvalB x Hxb), (HEvalA y Hya) in Hxy.
      apply OrdPair.Equal in Hxy. destruct Hxy as [H10 _].
      exact (Natural.ZeroIsNotOne (eq_sym H10)).
    - (* x, y both in b: (1,g!x) = (1,g!y) => g!x = g!y, then g injective.      *)
      rewrite (HEvalB x Hxb), (HEvalB y Hyb) in Hxy.
      apply OrdPair.Equal in Hxy. destruct Hxy as [_ Hgxy].
      exact (Bij.EvalInjective g b d x y Hg Hxb Hyb Hgxy). }
  (* h bijects a \/ b onto {0} x c \/ {1} x d. Composing with the bijection     *)
  (* {0} x c \/ {1} x d ~ c + d gives the required bijection a \/ b ~ c + d.    *)
  exists ((Plus2.f c d) :.: h).
  apply Bij.Compose with (sum c d).
  - apply Bij.FromFun; assumption.
  - apply Plus2.IsBij; assumption.
Qed.

(* If a is an ordinal with N <= a, then a is equipotent to its successor.       *)
Proposition Succ : forall (a:U), Ordinal a ->
  :N :<=: a -> a :~: succ a.
Proof.
  (* Proof by Claude + sonnet 4.6                                               *)
  (* succ(a) = a \/ {a} = {a} \/ a ~ 1 + a = a, so a ~ succ(a) by symmetry.     *)
  intros a Ha HN. apply Sym. unfold succ. rewrite Union2.Comm.
  (* {a} and a are disjoint: a in a would contradict the axiom of foundation.   *)
  assert (:{a}: :/\: a = :0:) as Hdisj. {
    apply Incl.Double. split. 2: apply Empty.IsIncl.
    intros x Hx. apply Inter2.Charac in Hx. destruct Hx as [Hxa Ha'].
    apply Single.Charac in Hxa. subst x. exfalso.
    revert Ha'. apply Foundation.NoLoop1. }
  apply Tran with (:1: :+: a).
  (* {a} \/ a ~ 1 + a via DisjointUnion, using {a} ~ 1 and a ~ a.               *)
  - apply DisjointUnion.
    + apply Natural.OneIsOrdinal.
    + exact Ha.
    + apply WhenSingle.
    + apply Refl.
    + exact Hdisj.
  (* 1 + a = a since 1 in N and N <= a, so the result follows.                  *)
  - rewrite (Plus.WhenNatL :1: a Ha Omega.HasOne HN). apply Refl.
Qed.

Proposition WellOrderableSuccRev : forall (a:U),
  WellOrderable (succ a) -> WellOrderable a.
Proof.
  intros a [c [H1 H2]].
  assert (c = :0: \/ Successor c \/ Limit c) as [H3|[H3|H3]]. {
    apply Limit.ThreeWay. assumption. }
  - exfalso. subst.
    assert (succ a = :0:) as H4. { apply WhenZero. assumption. }
    revert H4. apply Succ.NotZero.
  - destruct H3 as [b [H5 H4]]. subst.
    assert (a :~: b) as H6. { apply SuccCompatRev. assumption. }
    exists b. split; assumption.
  - assert (Ordinal c) as H4. { apply H3. }
    assert (:N :<=: c) as H5. { apply Omega.IsInclLimit. assumption. }
    assert (c :~: succ c) as H6. { apply Succ; assumption. }
    assert (succ a :~: succ c) as H7. { apply Tran with c; assumption. }
    assert (a :~: c) as H8. { apply SuccCompatRev. assumption. }
    exists c. split; assumption.
Qed.

(* The cartesian product is commutative up to equipotence.                      *)
Proposition ProdComm : forall (a b:U),
  a :x: b :~: b :x: a.
Proof.
  (* Proof by Claude + sonnet 4.6                                               *)
  (* Define h : a x b -> b x a by h(u,v) = (v,u).                               *)
  intros a b.
  remember (from2 a b (fun u v => :(v, u):)) as h eqn:Hh.
  assert (FunctionOn h (a :x: b)) as H1. { rewrite Hh. apply From2.IsFunctionOn. }
  (* By definition, for u in a and v in b, h(u,v) = (v,u).                      *)
  assert (forall u v, u :< a -> v :< b -> h!(:(u,v):) = :(v,u):) as G1. {
    intros u v Hu Hv. rewrite Hh. rewrite From2.Eval by assumption. reflexivity. }
  (* range h <= b x a: for (u,v) in a x b, h(u,v) = (v,u) lies in b x a.        *)
  assert (range h :<=: b :x: a) as H2. {
    intros y Hy.
    apply (FunctionOn.RangeCharac h (a :x: b)) in Hy. 2: assumption.
    destruct Hy as [p [Hp Hpy]].
    apply Prod.Charac in Hp. destruct Hp as [u [v [Hp [Hu Hv]]]].
    rewrite <- Hpy, Hp, (G1 u v Hu Hv).
    apply Prod.Charac2. split; assumption. }
  assert (Fun h (a :x: b) (b :x: a)) as H3. { split; assumption. }
  (* Surjectivity: for (v,u) in b x a, (u,v) lies in a x b and h(u,v) = (v,u).  *)
  assert (b :x: a :<=: range h) as H4. {
    intros z Hz.
    apply Prod.Charac in Hz. destruct Hz as [v [u [Hz [Hv Hu]]]].
    apply (FunctionOn.RangeCharac h (a :x: b)). 1: assumption.
    exists :(u,v):. split.
    - apply Prod.Charac2. split; assumption.
    - rewrite (G1 u v Hu Hv). symmetry. exact Hz. }
  (* Injectivity: h(u1,v1) = h(u2,v2) gives (v1,u1) = (v2,u2),                  *)
  (* so u1 = u2 and v1 = v2 by equality of ordered pairs.                       *)
  assert (OneToOne h) as H5. {
    apply (FunctionOn.IsOneToOne h (a :x: b)). 1: assumption.
    intros p q Hp Hq Hpq.
    apply Prod.Charac in Hp. destruct Hp as [u1 [v1 [Hp [Hu1 Hv1]]]].
    apply Prod.Charac in Hq. destruct Hq as [u2 [v2 [Hq [Hu2 Hv2]]]].
    rewrite Hp, Hq, (G1 u1 v1 Hu1 Hv1), (G1 u2 v2 Hu2 Hv2) in Hpq.
    apply OrdPair.Equal in Hpq. destruct Hpq as [Hveq Hueq].
    rewrite Hp, Hq, Hveq, Hueq. reflexivity. }
  exists h. apply Bij.FromFun; assumption.
Qed.

(* The product a x {b} of a set a and a singleton is equipotent to a.           *)
Proposition ProdSingleR : forall (a b:U),  a :x: :{b}: :~: a.
Proof.
  (* Proof by Claude + sonnet 4.6                                               *)
  (* a x {b} ~ {b} x a since the product is commutative, and {b} x a ~ a.       *)
  intros a b. apply Tran with (:{b}: :x: a).
  - apply ProdComm.
  - apply ProdSingleL.
Qed.

(* Any ordinal a containing N is equipotent to a + n for every natural n.       *)
Proposition WhenNatR : forall (n a:U), Ordinal a ->
  n :< :N -> :N :<=: a -> a :~: a :+: n.
Proof.
  (* Proof by Claude + sonnet 4.6                                               *)
  (* By induction on n.                                                         *)
  intros n a Ha Hn HN. revert n Hn.
  apply Omega.Induction.
  (* Base: a + 0 = a, so a ~ a + 0 trivially.                                   *)
  - rewrite Plus.WhenZeroR. apply Refl.
  (* Step: by induction a ~ a + n, and N <= a <= a + n, so Succ gives           *)
  (* a + n ~ succ(a + n) = a + succ(n). Transitivity completes the step.        *)
  - intros n Hn IH.
    assert (Ordinal n) as Hn_ord. { apply Omega.HasOrdinals. exact Hn. }
    rewrite (Plus.WhenSuccR a n Hn_ord).
    apply Tran with (a :+: n). 1: exact IH.
    apply Succ.
    + apply Plus.IsOrdinal. 1: exact Ha. exact Hn_ord.
    + apply Incl.Tran with a. 1: exact HN.
      apply Plus.IsInclR. 1: exact Ha. exact Hn_ord.
Qed.

(* For ordinals a and b, the cartesian product a x b is equipotent to a * b.    *)
Proposition ProdIsMult : forall (a b:U), Ordinal a -> Ordinal b ->
  a :x: b :~: a :*: b.
Proof.
  (* Proof by Claude + sonnet 4.6                                               *)
  (* a x b ~ b x a by commutativity, and b x a ~ a * b by the Mult2 bijection.  *)
  intros a b Ha Hb. apply Tran with (b :x: a).
  - apply ProdComm.
  - exists (Mult2.f a b). apply Mult2.IsBij; assumption.
Qed.

(* Equipotent natural numbers are equal.                                        *)
Proposition EqualNat : forall (m n:U), m :< :N -> n :< :N ->
  m :~: n -> m = n.
Proof.
  (* Proof by Claude + sonnet 4.6                                               *)
  (* Induction on n: define A n = "any m in N equipotent to n equals n".        *)
  remember (fun n => forall m, m :< :N -> m :~: n -> m = n) as A eqn:HA.
  assert (A :0:) as H1. {
    (* Base case: m :~: 0 implies m = 0.                                        *)
    rewrite HA. intros m H1 H2. apply WhenZero. assumption. }
  assert (forall n, n :< :N -> A n -> A (succ n)) as H2. {
    rewrite HA. intros n H2 IH m H3 H4.
    (* m :~: succ n and succ n is not 0, so m is not 0.                         *)
    assert (m <> :0:) as H5. {
      intros H5. subst. apply Sym in H4. apply WhenZero in H4.
      apply (Succ.NotZero n). assumption. }
    (* m :< N and m is not 0, so m = succ p for some p :< N.                    *)
    assert (exists p, p :< :N /\ m = succ p) as H6. {
      apply Omega.HasPred. 1: assumption.
      apply Omega.WhenNotZero; assumption. }
    destruct H6 as [p [H6 H7]].
    (* succ p :~: succ n, so p :~: n.                                           *)
    assert (p :~: n) as H8. {
      apply SuccCompatRev. rewrite <- H7. assumption. }
    (* By the inductive hypothesis, p = n, hence m = succ p = succ n.           *)
    assert (p = n) as H9. { apply IH; assumption. }
    rewrite H7, H9. reflexivity. }
  intros m n H3 H4 H5.
  assert (A n) as H6. { apply Omega.Induction; assumption. }
  rewrite HA in H6. apply H6; assumption.
Qed.

(* No natural number is equipotent to its successor.                            *)
Proposition NotSuccNat : forall (n:U), n :< :N ->
  ~ n :~: succ n.
Proof.
  (* Proof by Claude + sonnet 4.6                                               *)
  intros n H1 H2.
  (* succ n is also a natural number.                                           *)
  assert (succ n :< :N) as H3. { apply Omega.HasSucc. assumption. }
  (* Since n ~ succ n and both are naturals, they must be equal.                *)
  assert (n = succ n) as H4. { apply EqualNat; assumption. }
  (* But n lies in succ n, so n = succ n gives n in n, contradicting foundation.*)
  assert (n :< succ n) as H5. { apply Succ.IsIn. }
  rewrite <- H4 in H5. revert H5. apply Foundation.NoLoop1.
Qed.

(* No injection from succ n into n exists for any natural number n.             *)
Proposition NoInjSuccNat : forall (n:U), n :< :N ->
  ~ exists f, Inj f (succ n) n.
Proof.
  (* Proof by Claude + sonnet 4.6                                               *)
  intros n H1 [f [H2 H3]].
  (* f bijects succ n onto its range, which lies inside n.                      *)
  assert (succ n :~: range f) as H4. {
    exists f. split. 1: exact H2. reflexivity. }
  (* n is a subset of succ n.                                                   *)
  assert (n :<=: succ n) as H5. { apply Succ.IsIncl. }
  (* By Cantor-Schroeder-Bernstein, succ n is equipotent to n.                  *)
  assert (succ n :~: n) as H6. {
    apply CantorShroderBernstein with (range f) n; try assumption.
    apply Refl. }
  (* Hence n ~ succ n, contradicting NotSuccNat.                                *)
  apply (NotSuccNat n H1). apply Sym. assumption.
Qed.

(* An ordinal equipotent to a natural number equals that natural number.        *)
Proposition EqualOrdNat : forall (a n:U), Ordinal a -> n :< :N ->
  a :~: n -> a = n.
Proof.
  (* Proof by Claude + sonnet 4.6                                               *)
  intros a n H1 H2 H3.
  (* n is an ordinal since every element of N is an ordinal.                    *)
  assert (Ordinal n) as H4. { apply Omega.HasOrdinals. assumption. }
  (* Ordinal trichotomy: a = n, a :< n, or n :< a.                              *)
  assert (a = n \/ a :< n \/ n :< a) as H5. { apply Core.IsTotal; assumption. }
  destruct H5 as [H5|[H5|H5]]. 1: assumption.
  - (* a :< n implies a :< N, and two equipotent natural numbers are equal.     *)
    assert (a :< :N) as H6. { apply Omega.IsIn with n; assumption. }
    apply EqualNat; assumption.
  - (* n :< a implies succ n :<=: a; compose injections succ n -> a -> n        *)
    (* yielding an injection from succ n into n, which is impossible.           *)
    assert (succ n :<=: a) as H6. { apply Succ.ElemIsIncl; assumption. }
    destruct H3 as [f [H3 H3']].
    assert (Inj (id a :|: succ n) (succ n) a) as I1. {
      apply Inj.Restrict with a. 1: apply Id.IsInj. assumption. }
    assert (Inj f a n) as I2. { apply Bij.IsInj. split; assumption. }
    exfalso. apply (NoInjSuccNat n H2). exists (f :.: (id a :|: succ n)).
    apply Inj.Compose with a; assumption.
Qed.

