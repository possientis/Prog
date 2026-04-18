Require Import ZF.Axiom.Choice.
Require Import ZF.Axiom.Classic.
Require Import ZF.Class.Diff.
Require Import ZF.Class.Equiv.
Require Import ZF.Class.Inter2.
Require Import ZF.Class.Order.E.
Require Import ZF.Class.Ordinal.FunctionOn.
Require Import ZF.Class.Ordinal.Recursion.
Require Import ZF.Class.Proper.
Require Import ZF.Class.Relation.FunctionOn.
Require Import ZF.Class.Relation.OneToOne.
Require Import ZF.Class.Relation.ToFun.
Require Import ZF.Class.Small.
Require Import ZF.Set.Cardinal.Equiv.
Require Import ZF.Set.Core.
Require Import ZF.Set.Diff.
Require Import ZF.Set.Empty.
Require Import ZF.Set.Foundation.
Require Import ZF.Set.Incl.
Require Import ZF.Set.Order.Isom.
Require Import ZF.Set.Order.RestrictOfClass.
Require Import ZF.Set.Ordinal.Core.
Require Import ZF.Set.Ordinal.InfOfClass.
Require Import ZF.Set.Ordinal.Omega.
Require Import ZF.Set.Ordinal.Order.
Require Import ZF.Set.Ordinal.RecursionNOfClass.
Require Import ZF.Set.Ordinal.Succ.
Require Import ZF.Set.OrdPair.
Require Import ZF.Set.Power.
Require Import ZF.Set.Relation.Bij.
Require Import ZF.Set.Relation.Bijection.
Require Import ZF.Set.Relation.BijectionOn.
Require Import ZF.Set.Relation.Compose.
Require Import ZF.Set.Relation.Converse.
Require Import ZF.Set.Relation.Domain.
Require Import ZF.Set.Relation.Eval.
Require Import ZF.Set.Relation.EvalOfClass.
Require Import ZF.Set.Relation.Fun.
Require Import ZF.Set.Relation.Function.
Require Import ZF.Set.Relation.FunctionOn.
Require Import ZF.Set.Relation.Image.
Require Import ZF.Set.Relation.ImageByClass.
Require Import ZF.Set.Relation.Inj.
Require Import ZF.Set.Relation.OneToOne.
Require Import ZF.Set.Relation.Onto.
Require Import ZF.Set.Relation.Range.
Require Import ZF.Set.Relation.Restrict.
Require Import ZF.Set.Relation.RestrictOfClass.
Require Import ZF.Set.Relation.ToFun.
Require Import ZF.Set.Relation.ToFun2.

Require Import ZF.Notation.Eval.
Require Import ZF.Notation.Image.

Module CEM := ZF.Class.Empty.
Module CEQ := ZF.Class.Equiv.
Module CFO := ZF.Class.Relation.FunctionOn.
Module COF := ZF.Class.Ordinal.FunctionOn.
Module CRD := ZF.Class.Relation.Domain.
Module CRO := ZF.Class.Relation.OneToOne.
Module CRR := ZF.Class.Relation.Range.
Module CRT := ZF.Class.Relation.ToFun.
Module SOC := ZF.Set.Ordinal.Core.
Module SOI := ZF.Set.Ordinal.InfOfClass.
Module SOO := ZF.Set.Ordinal.Order.
Module SOR := ZF.Set.Ordinal.RecursionNOfClass.
Module SRI := ZF.Set.Relation.ImageByClass.
Module SRR := ZF.Set.Relation.RestrictOfClass.

(* The cardinal of a set is the smallest ordinal in bijection with it.         *)
Definition card (a:U) : U := inf (fun b => Ordinal b /\ a :~: b).

(* The class of all cardinal numbers.                                          *)
Definition Cardinal : Class := fun b => exists a, b = card a.

Proposition HasOrdinal : Choice ->
  forall (a:U), exists b, Ordinal b /\ a :~: b.
Proof.
  intros AC a. specialize (AC :P(a)). destruct AC as [f [H1 H2]].
  remember (fun x => f!(a :\: range x)) as G eqn:H3.
  remember (Recursion (CRT.toFun G)) as F eqn:H4.
  assert (forall x,
    a :\: range x <> :0: -> f!(a :\: range x) :< a :\: range x) as H5. {
      intros x H5. apply H2. 2: assumption.
      apply Power.Charac, Diff.IsIncl. }
  assert (forall b, Ordinal b -> F!b = :[G]:!(F:|:b)) as H6. {
    intros b H6. rewrite H4. apply Recursion.IsRecursive. assumption. }
  assert (forall b , Ordinal b ->
    a :\: range (F:|:b) <> :0: -> F!b :< a :\: range (F:|:b)) as H7. {
      intros b H7 H8. rewrite H6, CRT.Eval, H3. 2: assumption.
      apply H5. assumption. }
  assert (CFO.FunctionOn F Ordinal) as G1. {
    rewrite H4. apply Recursion.IsFunctionOn. }
  assert (Small (toClass a)) as G2. { apply Small.SetIsSmall. }
  assert (CRD.domain F :~: Ordinal) as G3. { apply G1. }
  assert (forall b, Ordinal b               ->
    (toClass a :\: toClass F:[b]:) :<>: :0: ->
    (toClass a :\: toClass F:[b]:) F!b) as H8. {
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
    (forall c, c :< b -> (toClass a :\: toClass F:[c]:) :<>: :0:) /\
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
  exists b. split. 1: assumption. apply Equiv.Sym. exists (F:|:b). assumption.
Qed.

Proposition WhenOrdinals : forall (a b:U), Ordinal b ->
  a :<=: b  -> exists c, Ordinal c /\ c :<=: b /\ a :~: c.
Proof.
  intros a b H1 H2.
  assert (exists c f,
    Ordinal c /\ c :<=: b /\ Isom f (E:/:c) (E:/:a) c a) as H3. {
      apply SOO.WhenOrdinals; assumption. }
  destruct H3 as [c [f [H3 [H4 H5]]]].
  exists c.
  assert (a :~: c) as H6. { apply Sym. exists f. apply H5. }
  split. 1: assumption. split; assumption.
Qed.

Proposition IsOrdinal : forall (a:U), Ordinal (card a).
Proof.
  intros a. apply SOI.IsOrdinal.
Qed.

Proposition IsLowerBound : forall (a b:U),
  Ordinal b       ->
  a :~: b         ->
  card a :<=: b.
Proof.
  intros a b H1 H2. apply SOI.IsLowerBound.
  - intros c H3. apply H3.
  - split; assumption.
Qed.

Proposition IsLargest : forall (a b:U),
  Choice                                        ->
  Ordinal b                                     ->
  (forall c, Ordinal c -> a :~: c -> b :<=: c)  ->
  b :<=: card a.
Proof.
  intros a b AC H1 H2.
  apply SOI.IsLargest.
  - intros c H3. apply H3.
  - assert (exists c, Ordinal c /\ a :~: c) as H3. { apply HasOrdinal. assumption. }
    destruct H3 as [c H3]. apply CEM.HasElem. exists c. assumption.
  - intros c [H3 H4]. apply H2; assumption.
Qed.

Lemma IsEquivGen : forall (a:U),
  (exists b, Ordinal b /\ a :~: b) -> a :~: card a.
Proof.
  intros a K1.
  remember (fun b => Ordinal b /\ a :~: b) as A eqn:H1.
  assert (A :<=: Ordinal) as H2. { rewrite H1. intros b H2. apply H2. }
  assert (A :<>: :0:) as H3. { apply CEM.HasElem. assumption. }
  assert (A (card a)) as H4. {
    unfold card. rewrite <- H1. apply SOI.IsIn; assumption. }
  rewrite H1 in H4. apply H4.
Qed.

Proposition IsEquivChoice : forall (a:U), Choice -> a :~: card a.
Proof.
  intros a AC. apply IsEquivGen, HasOrdinal. assumption.
Qed.

Proposition IsEquivOrd : forall (a:U), Ordinal a -> a :~: card a.
Proof.
  intros a H1.
  apply IsEquivGen. exists a. split. 1: assumption. apply Equiv.Refl.
Qed.

Proposition IsEquivNotZero : forall (a:U),
  card a <> :0: -> a :~: card a.
Proof.
  intros a H1.
  apply IsEquivGen. apply Classic.DoubleNegation. intros H2.
  apply H1. apply SOI.IsZero. intros x. split; intros H3. 2: contradiction.
  exfalso. apply H2. exists x. apply H3.
Qed.

Proposition IsNotEquiv : forall (a b:U), Ordinal b ->
  b :< card a -> a :<>: b.
Proof.
  intros a b H1 H2 H3.
  assert (card a :<=: b) as H4. { apply IsLowerBound; assumption. }
  assert (b :< b) as H5. { apply H4. assumption. }
  revert H5. apply NoElemLoop1.
Qed.

Proposition IsIncl : forall (a:U), Ordinal a -> card a :<=: a.
Proof.
  intros a H1. apply IsLowerBound. 1: assumption. apply Equiv.Refl.
Qed.

Proposition CardIsOrd : Cardinal :<=: Ordinal.
Proof.
  intros b [a H1]. subst. apply IsOrdinal.
Qed.

Proposition WhenCardinal : forall (a:U), Cardinal a <-> a = card a.
Proof.
  intros a. split; intros H1.
  - destruct H1 as [b H1].
    assert (Ordinal a) as G1. { rewrite H1. apply IsOrdinal. }
    assert (Ordinal (card a)) as G2. { apply IsOrdinal. }
    apply Incl.DoubleInclusion. split.
    + assert (a = :0: \/ :0: :< a) as H2. { apply SOC.ZeroOrElem. assumption. }
      destruct H2 as [H2|H2].
      * rewrite H2. apply SOC.IsIncl. rewrite <- H2. assumption.
      * remember (card a) as c eqn:H3. rewrite H1, H3.
        apply IsLowerBound. 1: apply IsOrdinal.
        apply Equiv.Tran with a.
        { rewrite H1. apply IsEquivNotZero. rewrite <- H1.
          apply Empty.HasElem. exists :0:. assumption. }
        { apply IsEquivOrd. assumption. }
    + apply IsIncl. assumption.
  - exists a. assumption.
Qed.

Proposition EquivCharac : Choice -> forall (a b:U),
  a :~: b <-> card a = card b.
Proof.
  intros AC a b. split; intros H1.
  - assert (card b :<=: card a) as H2. {
      apply IsLowerBound. 1: apply IsOrdinal.
      apply Equiv.Tran with a.
      + apply Equiv.Sym. assumption.
      + apply IsEquivChoice. assumption. }
    assert (card a :<=: card b) as H3. {
      apply IsLowerBound. 1: apply IsOrdinal.
      apply Equiv.Tran with b. 1: assumption.
      apply IsEquivChoice. assumption. }
    apply Incl.DoubleInclusion. split; assumption.
  - apply Equiv.Tran with (card a).
    + apply IsEquivChoice. assumption.
    + rewrite H1. apply Equiv.Sym, IsEquivChoice. assumption.
Qed.

Proposition Idem : forall (a:U), card (card a) = card a.
Proof.
  intros a. symmetry. apply WhenCardinal. exists a. reflexivity.
Qed.

Proposition InclCompat : forall (a b:U), Choice ->
  a :<=: b -> card a :<=: card b.
Proof.
  intros a b AC H1.
  assert (b :~: card b) as H2. { apply IsEquivChoice. assumption. }
  destruct H2 as [f H2].
  assert (exists x, x :<=: card b /\ a :~: x) as H3. {
    exists f:[a]:.
    assert (f:[a]: :<=: card b) as H3. {
      intros y H3.
      apply (Bij.ImageCharac f b (card b)) in H3. 2: assumption.
      destruct H3 as [x [H3 [H4 H5]]].
      apply (Bij.RangeCharac f b (card b)). 1: assumption.
      exists x. split; assumption. }
    assert (a :~: f:[a]:) as H4. {
      exists (f:|:a). apply (Bij.Restrict f b (card b)); assumption. }
    split; assumption. }
  destruct H3 as [x [H3 H4]].
  assert (exists c, Ordinal c /\ c :<=: card b /\ x :~: c) as H5. {
    apply WhenOrdinals. 2: assumption. apply IsOrdinal. }
  destruct H5 as [c [H5 [H6 H7]]].
  assert (card a = card x) as H8. { apply EquivCharac; assumption. }
  assert (card x = card c) as H9. { apply EquivCharac; assumption. }
  assert (card c :<=: c) as H10. { apply IsIncl. assumption. }
  rewrite H8, H9. apply Incl.Tran with c; assumption.
Qed.

Proposition CantorShroderBernsteinChoice : forall (a b c d:U),
  Choice    ->
  a :~: c   ->
  b :~: d   ->
  c :<=: b  ->
  d :<=: a  ->
  a :~: b.
Proof.
  intros a b c d AC H1 H2 H3 H4.
  assert (card a = card c) as H5. { apply EquivCharac; assumption. }
  assert (card b = card d) as H6. { apply EquivCharac; assumption. }
  assert (card c :<=: card b) as H7. { apply InclCompat; assumption. }
  assert (card d :<=: card a) as H8. { apply InclCompat; assumption. }
  apply EquivCharac. assumption. apply Incl.DoubleInclusion. split.
  - rewrite H5. assumption.
  - rewrite H6. assumption.
Qed.

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
  remember (SOR.recursion (CRT.toFun H) (a :\: d)) as h eqn:H6.
  assert (FunctionOn h :N) as H7. { rewrite H6. apply SOR.IsFunctionOn. }
  assert (h!:0: = a :\: d) as H8. { rewrite H6. apply SOR.WhenZero. }
  assert (forall n, n :< :N -> h!(succ n) = (g :.: f) :[h!n]:) as H9. {
    intros n H9. rewrite H6, SOR.WhenSucc, <- H6, CRT.Eval, H5.
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
  remember (toFun2 a A (fun x => f!x) (fun x => g^:-1:!x)) as k eqn:H16.
  assert (forall x n, ~ A x -> n :< :N -> ~ x :< h!n) as H17. {
    rewrite H15.
    intros x n H17 H18 H19. apply H17. exists n; split; assumption. }
  assert (FunctionOn k a) as H18. { rewrite H16. apply ToFun2.IsFunctionOn. }
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
    - rewrite H16, ToFun2.Eval1; try assumption.
      apply H3, Bij.IsInRange with a; assumption.
    - rewrite H16, ToFun2.Eval2; try assumption.
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
        rewrite H16, ToFun2.Eval1; try assumption.
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
        rewrite H16, ToFun2.Eval2; try assumption. reflexivity. }
      rewrite (Bij.ConverseEvalOfEval g b d) in H31; try assumption.
      exists g!y. split; assumption. }
  assert (range k = b) as H26. {
    apply Incl.DoubleInclusion. split; assumption. }
  assert (domain k = a) as G5. { apply H24. }
  assert (forall x y, x :< a -> y :< a -> k!x = k!y -> A x -> A y) as H27. {
    intros x y H27 H28 H29 H30. apply Classic.DoubleNegation. intros H31.
    assert (k!x = f!x) as H32. {
      rewrite H16, ToFun2.Eval1; try assumption. reflexivity. }
    assert(k!y = g^:-1:!y) as H33. {
      rewrite H16, ToFun2.Eval2; try assumption. reflexivity. }
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
        rewrite H16, ToFun2.Eval1; try assumption. reflexivity. }
      assert (k!y = f!y) as H34. {
        rewrite H16, ToFun2.Eval1; try assumption. reflexivity. }
      rewrite H33, H34 in H30.
      apply (Bij.EvalInjective f a c); assumption.
    - assert (~ A y) as H32. {
        intros H32.
        assert (A x) as H33. {
          apply H27 with y; try assumption. symmetry. assumption. }
        contradiction. }
      assert (k!x = g^:-1:!x) as H33. {
        rewrite H16, ToFun2.Eval2; try assumption. reflexivity. }
      assert (k!y = g^:-1:!y) as H34. {
        rewrite H16, ToFun2.Eval2; try assumption. reflexivity. }
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

Proposition PowerCompat : forall (a b:U),
  a :~: b -> :P(a) :~: :P(b).
Proof.
  intros a b [f H1].
  assert (Fun f a b) as G1. { apply Bij.IsFun. assumption. }
  assert (domain f = a) as G2. { apply H1. }
  assert (Bij f^:-1: b a) as G3. { apply Bij.Converse. assumption. }
  remember (toFun :P(a) (fun x => f:[x]:)) as g eqn:H2.
  assert (FunctionOn g :P(a)) as H3. { rewrite H2. apply ToFun.IsFunctionOn. }
  assert (range g :<=: :P(b)) as H4. {
    intros y H4.
    apply (FunctionOn.RangeCharac g :P(a)) in H4. 2: assumption.
    destruct H4 as [x [H4 H5]]. rewrite H2, ToFun.Eval in H5. 2: assumption.
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
      rewrite H2, ToFun.Eval, ToFun.Eval in H13; try assumption.
      apply Power.Charac in H11. apply Power.Charac in H12.
      apply DoubleInclusion. split; intros z H14.
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
      rewrite H2, ToFun.Eval, <- H13. 2: assumption. reflexivity. }
    assert (g!x = y) as H16. {
      rewrite (Bij.ImageOfInvImage f a b) in H15; try assumption.
      apply Power.Charac in H12. assumption. }
      apply (Fun.RangeCharac g :P(a) :P(b)). 1: assumption.
      exists x. split; assumption. }
  assert (Bij g :P(a) :P(b)) as H13. { apply Bij.FromFun; assumption. }
  exists g. assumption.
Qed.
