Require Import ZF.Axiom.Choice.
Require Import ZF.Class.Equiv.
Require Import ZF.Class.Incl.
Require Import ZF.Class.Proper.
Require Import ZF.Class.Small.
Require Import ZF.Set.Core.
Require Import ZF.Set.Cardinal.Core.
Require Import ZF.Set.Cardinal.Hartogs.
Require Import ZF.Set.Ordinal.Core.
Require Import ZF.Set.Foundation.
Require Import ZF.Set.Power.
Require Import ZF.Set.Relation.Id.
Require Import ZF.Set.Relation.Inj.
Require Import ZF.Set.Union.

Module SCC := ZF.Set.Cardinal.Core.

(* There is always a cardinal number larger than all cardinals of a given set.  *)
Proposition LargerCardinalChoice : forall (a:U),
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
    assert (Ordinal (card :U(a))) as H7. { apply SCC.IsOrdinal. }
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

(* There is always a cardinal number larger than all cardinals of a given set.  *)
Proposition LargerCardinal : forall (a:U),
  toClass a :<=: Cardinal                               ->
  exists b, Cardinal b /\ forall c, c :< a -> c :< b.
Proof.
  (* Proof by Claude.                                                           *)
  (* Let b = hartogs(U(a)). For any cardinal c in a, c is a subset of U(a)      *)
  (* (each member of c is a member of some member of a). The identity on U(a)   *)
  (* restricts to an injection from c into U(a). Since c is an ordinal          *)
  (* injecting into U(a), c is an element of hartogs(U(a)) = b.                 *)
  intros a H1.
  remember (hartogs :U(a)) as b eqn:H2. exists b.
  assert (Cardinal b) as H3. {
    rewrite H2. apply Hartogs.IsCardinal. }
  assert (forall c, c :< a -> c :< b) as H4. {
    intros c H4.
    assert (Cardinal c) as H5. { apply H1. assumption. }
    assert (Ordinal c) as H6. { apply SCC.CardIsOrd. assumption. }
    assert (c :<=: :U(a)) as H7. {
      intros x H7. apply Union.Charac. exists c. split; assumption. }
    assert (Inj (id c) c (:U(a))) as H8. {
      split.
      - apply Id.IsBijectionOn.
      - rewrite Id.RangeOf. assumption. }
    rewrite H2. apply Hartogs.Charac. split.
    1: assumption. exists (id c). assumption. }
  split; assumption.
Qed.

(* The class of cardinal numbers is a proper class.                             *)
Proposition IsProperChoice : Choice -> Proper Cardinal.
Proof.
  intros AC H1. apply Small.IsSomeSet in H1. destruct H1 as [a H1].
  assert (toClass a :<=: Cardinal) as H2. { intros x H2. apply H1. assumption. }
  assert (exists b, Cardinal b /\ forall c, c :< a -> c :< b) as H3. {
    apply LargerCardinalChoice; assumption. }
  destruct H3 as [b [H3 H4]].
  assert (b :< a) as H5. { apply H1. assumption. }
  assert (b :< b) as H6. { apply H4. assumption. }
  revert H6. apply NoElemLoop1.
Qed.

(* The class of cardinal numbers is a proper class.                             *)
Proposition IsProper : Proper Cardinal.
Proof.
  (* Proof by Claude.                                                           *)
  (* If Cardinal were small it would equal the class of elements of some set a. *)
  (* By LargerCardinal there exists a cardinal b larger than every c in a.      *)
  (* But b is itself a cardinal so b is in a, giving b < b, contradicting       *)
  (* foundation.                                                                *)
  intros H1. apply Small.IsSomeSet in H1. destruct H1 as [a H1].
  assert (toClass a :<=: Cardinal) as H2. {
    intros x H2. apply H1. assumption. }
  assert (exists b, Cardinal b /\ forall c, c :< a -> c :< b) as H3. {
    apply LargerCardinal. assumption. }
  destruct H3 as [b [H3 H4]].
  assert (b :< a) as H5. { apply H1. assumption. }
  assert (b :< b) as H6. { apply H4. assumption. }
  revert H6. apply NoElemLoop1.
Qed.
