Require Import ZF.Axiom.Choice.
Require Import ZF.Class.Equiv.
Require Import ZF.Class.Proper.
Require Import ZF.Set.Cardinal.Equiv.
Require Import ZF.Set.Core.
Require Import ZF.Set.Empty.
Require Import ZF.Set.Foundation.
Require Import ZF.Set.Incl.
Require Import ZF.Set.Ordinal.Core.
Require Import ZF.Set.Ordinal.InfOfClass.
Require Import ZF.Set.Power.
Require Import ZF.Set.Relation.RestrictOfClass.
Require Import ZF.Set.Union.

Require Import ZF.Notation.Eval.
Require Import ZF.Notation.Image.

Module CEM := ZF.Class.Empty.
Module SOC := ZF.Set.Ordinal.Core.
Module SOI := ZF.Set.Ordinal.InfOfClass.

(* The cardinal of a set is the smallest ordinal in bijection with it.         *)
Definition card (a:U) : U := inf (fun b => Ordinal b /\ a :~: b).

(* The class of all cardinal numbers.                                          *)
Definition Cardinal : Class := fun b => exists a, b = card a.

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
  - assert (exists c, Ordinal c /\ a :~: c) as H3. {
      apply Equiv.HasOrdinal. assumption. }
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
    apply Equiv.OrdinalSubset. 2: assumption. apply IsOrdinal. }
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

Proposition Cantor : forall (a:U), Choice ->
  card a :< card :P(a).
Proof.
  intros a AC.
  assert (exists b, Ordinal b /\ a :~: b) as H1. {
    apply HasOrdinal. assumption. }
  destruct H1 as [b [H1 H2]].
  assert (Ordinal (card b)) as G1. { apply IsOrdinal. }
  assert (Ordinal (card :P(b))) as G2. { apply IsOrdinal. }
  assert (card a = card b) as H3. { apply EquivCharac; assumption. }
  assert (card :P(a) = card :P(b)) as H4. {
    apply EquivCharac, Equiv.PowerCompat; assumption. }
  assert (card b :< card :P(b)) as H5. {
    assert (b :<=: :P(b)) as H5. {
      intros c H5.
      assert (Ordinal c) as K1. { apply SOC.IsOrdinal with b; assumption. }
      apply Power.Charac. intros d H6.
      assert (Ordinal d) as K2. { apply SOC.IsOrdinal with c; assumption. }
      apply SOC.ElemElemTran with c; assumption. }
  assert (card b :<=: card :P(b)) as H6. { apply InclCompat; assumption. }
  assert (card b = card :P(b) \/ card b :< card :P(b)) as H7. {
    apply SOC.EqualOrElem; assumption. }
  destruct H7 as [H7|H7]. 2:assumption. exfalso.
  assert (b :~: :P(b)) as H8. { apply EquivCharac; assumption. }
  apply Equiv.Cantor with b. assumption. }
  rewrite H3, H4. assumption.
Qed.

(* There is always a cardinal number larger than all cardinals of a given set.  *)
Proposition LargerCardinal : forall (a:U),
  Choice                                                ->
  toClass a :<=: Cardinal                               ->
  exists b, Cardinal b /\ forall c, c :< a -> c :< b.
Proof.
  intros a AC H1.
  remember (card :P(:U(a))) as b eqn:H2. exists b.
  assert (Cardinal b) as H3. { exists :P(:U(a)). assumption. }
  assert (forall c, c :< a -> c :< b) as H4. {
    intros c H4.
    assert (Cardinal c) as H5. { apply H1. assumption. }
    assert (Ordinal c) as H6. { apply CardIsOrd. assumption. }
    assert (Ordinal (card :U(a))) as H7. { apply IsOrdinal. }
    assert (Ordinal b) as H8. { apply CardIsOrd. assumption. }
    assert (card :U(a) :< b) as H9. { rewrite H2. apply Cantor. assumption. }
    assert (c :<=: card :U(a)) as H10. {
      assert (c :<=: :U(a)) as H10. {
        intros x H10. apply Union.Charac. exists c. split; assumption. }
      assert (c = card c) as H11. { apply WhenCardinal. assumption. }
      rewrite H11. apply InclCompat; assumption. }
    apply SOC.InclElemTran with (card :U(a)); assumption. }
  split; assumption.
Qed.

(* The class of cardinal numbers is a proper class.                             *)
Proposition IsProper : Choice -> Proper Cardinal.
Proof.
  intros AC H1. apply Small.IsSomeSet in H1. destruct H1 as [a H1].
  assert (toClass a :<=: Cardinal) as H2. { intros x H2. apply H1. assumption. }
  assert (exists b, Cardinal b /\ forall c, c :< a -> c :< b) as H3. {
    apply LargerCardinal; assumption. }
  destruct H3 as [b [H3 H4]].
  assert (b :< a) as H5. { apply H1. assumption. }
  assert (b :< b) as H6. { apply H4. assumption. }
  revert H6. apply NoElemLoop1.
Qed.

