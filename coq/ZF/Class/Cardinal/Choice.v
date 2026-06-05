Require Import ZF.Axiom.Choice.
Require Import ZF.Class.Equiv.
Require Import ZF.Class.Incl.
Require Import ZF.Class.Proper.
Require Import ZF.Set.Cardinal.Choice.
Require Import ZF.Set.Cardinal.Core.
Require Import ZF.Set.Core.
Require Import ZF.Set.FromClass.
Require Import ZF.Set.Ordinal.Core.
Require Import ZF.Set.Power.
Require Import ZF.Set.Union.

Module SCC := ZF.Set.Cardinal.Core.
Module SCH := ZF.Set.Cardinal.Choice.

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
    assert (Ordinal c) as H6. { apply SCC.CardIsOrd. assumption. }
    assert (Ordinal (card :U(a))) as H7. { apply SCC.IsOrdinal. }
    assert (Ordinal b) as H8. { apply SCC.CardIsOrd. assumption. }
    assert (card :U(a) :< b) as H9. { rewrite H2. apply SCH.Cantor. assumption. }
    assert (c :<=: card :U(a)) as H10. {
      assert (c :<=: :U(a)) as H10. {
        intros x H10. apply Union.Charac. exists c. split; assumption. }
      assert (c = card c) as H11. { apply WhenCardinal. assumption. }
      rewrite H11. apply SCH.InclCompat; assumption. }
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
  revert H6. apply Foundation.NoLoop1.
Qed.
