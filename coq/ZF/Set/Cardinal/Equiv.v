Require Import ZF.Axiom.Choice.
Require Import ZF.Axiom.Classic.
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
Require Import ZF.Set.Order.E.
Require Import ZF.Set.Order.Isom.
Require Import ZF.Set.Order.RestrictOfClass.
Require Import ZF.Set.Ordinal.Core.
Require Import ZF.Set.Ordinal.Mult.
Require Import ZF.Set.Ordinal.Mult2.
Require Import ZF.Set.Ordinal.Natural.
Require Import ZF.Set.Ordinal.Omega.
Require Import ZF.Set.Ordinal.Order.
Require Import ZF.Set.Ordinal.Plus.
Require Import ZF.Set.Ordinal.Plus2.
Require Import ZF.Set.Ordinal.RecursionNOfClass.
Require Import ZF.Set.Ordinal.Succ.
Require Import ZF.Set.OrdPair.
Require Import ZF.Set.Power.
Require Import ZF.Set.Prod.
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
Require Import ZF.Set.Relation.ImageByClass.
Require Import ZF.Set.Relation.Inj.
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

Definition equiv (a b:U) : Prop := exists f, Bij f a b.

(* Notation "a :~: b" := (equiv a b)                                            *)
Global Instance Equiv : Equiv U := { equiv := equiv }.

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

(* Assuming choice, every set is equipotent to some ordinal.                    *)
Proposition HasOrdinal : Choice ->
  forall (a:U), exists b, Ordinal b /\ a :~: b.
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
    apply Incl.DoubleInclusion. split; assumption. }
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
      rewrite H2, From.Eval, <- H13. 2: assumption. reflexivity. }
    assert (g!x = y) as H16. {
      rewrite (Bij.ImageOfInvImage f a b) in H15; try assumption.
      apply Power.Charac in H12. assumption. }
      apply (Fun.RangeCharac g :P(a) :P(b)). 1: assumption.
      exists x. split; assumption. }
  assert (Bij g :P(a) :P(b)) as H13. { apply Bij.FromFun; assumption. }
  exists g. assumption.
Qed.

(* No set is equivalent to its power set.                                       *)
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
  - destruct H1 as [f H1]. apply Incl.DoubleInclusion. split; intros x H2.
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
  (* Proof by Claude.                                                           *)
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
      apply Incl.DoubleInclusion. split. 2: apply Union2.IsInclL.
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
            apply Foundation.NoElemLoop1.
          - exfalso. apply Single.Charac in H8.
            assert (f!x = a) as H11. { apply G2. assumption. }
            assert (f!y = y) as H12. { apply G1. assumption. }
            rewrite <- H12, <- H10, H11 in H9. revert H9.
            apply Foundation.NoElemLoop1.
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
      apply OrdPair.WhenEqual in H8. apply H8. }
    assert (Bij f a (:{b}: :x: a)) as H7. { apply Bij.FromFun; assumption. }
    exists f. assumption. }
  apply Sym. assumption.
Qed.

(* Equipotence is compatible with cartesian products.                           *)
Proposition ProdCompat : forall (a b c d:U),
  a :~: c -> b :~: d -> a :x: b :~: c :x: d.
Proof.
  (* Proof by Claude.                                                           *)
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
    apply OrdPair.WhenEqual in Hpq. destruct Hpq as [Hf Hg].
    apply (Bij.EvalInjective f a c u1 u2 H1 Hu1 Hu2) in Hf.
    apply (Bij.EvalInjective g b d v1 v2 H2 Hv1 Hv2) in Hg.
    rewrite Hp, Hq, Hf, Hg. reflexivity. }
  exists h. apply Bij.FromFun; assumption.
Qed.

(* Equipotence is left-compatible with cartesian product.                       *)
Proposition ProdCompatL : forall (a b c:U),
  a :~: b -> a :x: c :~: b :x: c.
Proof.
  (* Proof by Claude.                                                           *)
  (* If a ~ b then a x c ~ b x c.                                               *)
  intros a b c H.
  exact (ProdCompat a c b c H (Refl c)).
Qed.

(* Equipotence is right-compatible with cartesian product.                      *)
Proposition ProdCompatR : forall (a b c:U),
  a :~: b -> c :x: a :~: c :x: b.
Proof.
  (* Proof by Claude.                                                           *)
  (* If a ~ b then c x a ~ c x b.                                               *)
  intros a b c H.
  exact (ProdCompat c a c b (Refl c) H).
Qed.

(* Equipotence is compatible with the successor operation.                      *)
Proposition SuccCompat : forall (a b:U),
  a :~: b ->  succ a :~: succ b.
Proof.
  (* Proof by Claude.                                                           *)
  (* Let f : a -> b be the bijection given by the hypothesis.                   *)
  intros a b [f H1].
  (* Define h : succ(a) -> succ(b) by h(a) = b and h(x) = f(x) for x in a.      *)
  remember (fun x => x = a) as A eqn:H2.
  remember (ifThenElse (succ a) A (fun _ => b) (fun x => f!x)) as h eqn:H3.
  assert (FunctionOn h (succ a)) as H4. {
    rewrite H3. apply IfThenElse.IsFunctionOn. }
  (* For x in a, x ≠ a by the axiom of foundation, so h(x) = f(x).              *)
  assert (forall x, x :< a -> h!x = f!x) as G1. {
    intros x G1. rewrite H3, IfThenElse.Eval2. 1: reflexivity.
    - apply Succ.Charac. right. assumption.
    - rewrite H2. intros G2. subst. revert G1. apply Foundation.NoElemLoop1. }
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
  (* Injectivity: four cases. x = y = a is trivial. If x = a and y in a,        *)
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
      rewrite <- H10 in H11. revert H11. apply Foundation.NoElemLoop1.
    - subst. exfalso.
      rewrite (G1 x H8), G2 in H10.
      assert (f!x :< b) as H11. { exact (Bij.IsInRange f a b x H1 H8). }
      rewrite H10 in H11. revert H11. apply Foundation.NoElemLoop1.
    - rewrite (G1 x H8), (G1 y H9) in H10.
      exact (Bij.EvalInjective f a b x y H1 H8 H9 H10). }
  exists h. apply Bij.FromFun; assumption.
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
  (* Proof by Claude.                                                           *)
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
  assert (range h :<=: Plus2.sum c d) as HRangeIncl. {
    intros e He.
    apply (FunctionOn.RangeCharac h (a :\/: b)) in He. 2: assumption.
    destruct He as [x [Hx Hxe]].
    apply Union2.Charac in Hx. destruct Hx as [Hxa | Hxb].
    - rewrite HEvalA in Hxe. 2: assumption. subst e.
      unfold Plus2.sum. apply Union2.IsInclL.
      apply Prod.Charac2. split. 1: apply Single.IsIn.
      apply Bij.IsInRange with a; assumption.
    - rewrite HEvalB in Hxe. 2: assumption. subst e.
      unfold Plus2.sum. apply Union2.IsInclR.
      apply Prod.Charac2. split. 1: apply Single.IsIn.
      apply Bij.IsInRange with b; assumption. }
  assert (Fun h (a :\/: b) (Plus2.sum c d)) as HFun. { split; assumption. }
  (* Surjectivity: {0} x c \/ {1} x d <= range h.                               *)
  (* Every element of {0} x c \/ {1} x d is (0,e') with e' in c, or             *)
  (* (1,e') with e' in d. Surjectivity of f (resp. g) supplies the preimage.    *)
  assert (Plus2.sum c d :<=: range h) as HSurj. {
    intros p Hp. unfold Plus2.sum in Hp.
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
    apply (Fun.IsOneToOne h (a :\/: b) (Plus2.sum c d)). 1: assumption.
    intros x y Hx Hy Hxy.
    apply Union2.Charac in Hx. apply Union2.Charac in Hy.
    destruct Hx as [Hxa | Hxb]; destruct Hy as [Hya | Hyb].
    - (* x, y both in a: (0,f!x) = (0,f!y) => f!x = f!y, then f injective.      *)
      rewrite (HEvalA x Hxa), (HEvalA y Hya) in Hxy.
      apply OrdPair.WhenEqual in Hxy. destruct Hxy as [_ Hfxy].
      exact (Bij.EvalInjective f a c x y Hf Hxa Hya Hfxy).
    - (* x in a, y in b: (0,f!x) = (1,g!y) => 0 = 1, a contradiction.           *)
      exfalso.
      rewrite (HEvalA x Hxa), (HEvalB y Hyb) in Hxy.
      apply OrdPair.WhenEqual in Hxy. destruct Hxy as [H01 _].
      exact (Natural.ZeroIsNotOne H01).
    - (* x in b, y in a: (1,g!x) = (0,f!y) => 1 = 0, a contradiction.           *)
      exfalso.
      rewrite (HEvalB x Hxb), (HEvalA y Hya) in Hxy.
      apply OrdPair.WhenEqual in Hxy. destruct Hxy as [H10 _].
      exact (Natural.ZeroIsNotOne (eq_sym H10)).
    - (* x, y both in b: (1,g!x) = (1,g!y) => g!x = g!y, then g injective.      *)
      rewrite (HEvalB x Hxb), (HEvalB y Hyb) in Hxy.
      apply OrdPair.WhenEqual in Hxy. destruct Hxy as [_ Hgxy].
      exact (Bij.EvalInjective g b d x y Hg Hxb Hyb Hgxy). }
  (* h bijects a \/ b onto {0} x c \/ {1} x d. Composing with the bijection     *)
  (* {0} x c \/ {1} x d ~ c + d gives the required bijection a \/ b ~ c + d.    *)
  exists ((Plus2.f c d) :.: h).
  apply Bij.Compose with (Plus2.sum c d).
  - apply Bij.FromFun; assumption.
  - apply Plus2.IsBij; assumption.
Qed.

(* The cartesian product is commutative up to equipotence.                      *)
Proposition ProdComm : forall (a b:U),
  a :x: b :~: b :x: a.
Proof.
  (* Proof by Claude.                                                           *)
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
    apply OrdPair.WhenEqual in Hpq. destruct Hpq as [Hveq Hueq].
    rewrite Hp, Hq, Hveq, Hueq. reflexivity. }
  exists h. apply Bij.FromFun; assumption.
Qed.

(* The product a x {b} of a set a and a singleton is equipotent to a.           *)
Proposition ProdSingleR : forall (a b:U),  a :x: :{b}: :~: a.
Proof.
  (* Proof by Claude.                                                           *)
  (* a x {b} ~ {b} x a since the product is commutative, and {b} x a ~ a.       *)
  intros a b. apply Tran with (:{b}: :x: a).
  - apply ProdComm.
  - apply ProdSingleL.
Qed.

(* If a is an ordinal with N <= a, then a is equipotent to its successor.       *)
Proposition Succ : forall (a:U), Ordinal a ->
  :N :<=: a -> a :~: succ a.
Proof.
  (* Proof by Claude.                                                           *)
  (* succ(a) = a \/ {a} = {a} \/ a ~ 1 + a = a, so a ~ succ(a) by symmetry.     *)
  intros a Ha HN. apply Sym. unfold succ. rewrite Union2.Comm.
  (* {a} and a are disjoint: a in a would contradict the axiom of foundation.   *)
  assert (:{a}: :/\: a = :0:) as Hdisj. {
    apply Incl.DoubleInclusion. split. 2: apply Empty.IsIncl.
    intros x Hx. apply Inter2.Charac in Hx. destruct Hx as [Hxa Ha'].
    apply Single.Charac in Hxa. subst x. exfalso.
    revert Ha'. apply Foundation.NoElemLoop1. }
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

(* Any ordinal a containing N is equipotent to a + n for every natural n.       *)
Proposition WhenNatR : forall (n a:U), Ordinal a ->
  n :< :N -> :N :<=: a -> a :~: a :+: n.
Proof.
  (* Proof by Claude.                                                           *)
  (* By induction on n.                                                         *)
  intros n a Ha Hn HN. revert n Hn.
  apply Omega.Induction.
  (* Base: a + 0 = a, so a ~ a + 0 trivially.                                   *)
  - rewrite Plus.WhenZeroR. apply Refl.
  (* Step: by induction a ~ a + n, and N <= a <= a + n, so Succ gives           *)
  (* a + n ~ succ(a + n) = a + succ(n). Transitivity completes the step.        *)
  - intros n Hn IH.
    assert (Ordinal n) as Hn_ord. { apply Omega.HasOrdinalElem. exact Hn. }
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
  (* Proof by Claude.                                                           *)
  (* a x b ~ b x a by commutativity, and b x a ~ a * b by the Mult2 bijection.  *)
  intros a b Ha Hb. apply Tran with (b :x: a).
  - apply ProdComm.
  - exists (Mult2.f a b). apply Mult2.IsBij; assumption.
Qed.

