Require Import ZF.Class.Equiv.
Require Import ZF.Class.Incl.
Require Import ZF.Class.Order.Isom.
Require Import ZF.Class.Order.Restrict.
Require Import ZF.Class.Order.WellOrdering.
Require Import ZF.Class.Ordinal.Order.WFWO.
Require Import ZF.Class.Ordinal.Order.OnSubclass.
Require Import ZF.Class.Small.
Require Import ZF.Set.Core.
Require Import ZF.Set.Incl.
Require Import ZF.Set.Order.Isom.
Require Import ZF.Set.Order.WellOrdering.
Require Import ZF.Set.Ordinal.Core.
Require Import ZF.Set.Ordinal.Monotone.
Require Import ZF.Set.Ordinal.Order.E.
Require Import ZF.Set.Relation.Domain.
Require Import ZF.Set.Relation.Eval.
Require Import ZF.Set.Relation.Range.
Require Import ZF.Set.Relation.RestrictOfClass.

Module COI := ZF.Class.Order.Isom.
Module COW := ZF.Class.Order.WellOrdering.
Module COS := ZF.Class.Ordinal.Order.OnSubclass.
Module COO := ZF.Class.Ordinal.Order.WFWO.

Module SOE := ZF.Set.Ordinal.Order.E.
Module SOI := ZF.Set.Order.Isom.
Module SOW := ZF.Set.Order.WellOrdering.

Proposition Exists : forall (r b:U),
  WellOrdering r b          ->

  exists f a,
    Ordinal a               /\
    Isom f (E a) r a b.
Proof.
  intros r b H1.
  assert (COW.WellOrdering (toClass r) (toClass b)) as H2. { assumption. }
  assert (Small (toClass b)) as H3. { apply SetIsSmall. }
  assert (exists a, Ordinal a /\ forall (g:U),
    g = (COO.RecurseSmallestFresh (toClass r) (toClass b) :|: a) ->
    COI.Isom (toClass g) COE.E (toClass r) (toClass a) (toClass b)) as H4. {
      apply COO.WhenSmall; assumption. }
  destruct H4 as [a [H4 H5]].
  remember (COO.RecurseSmallestFresh (toClass r) (toClass b) :|: a) as f eqn:H6.
  exists f. exists a. split. 1: assumption. apply SOI.FromClass.
  apply COI.EquivCompat2 with (COE.E:/:toClass a).
  - apply Equiv.Sym, SOE.ToClass.
  - apply (proj1 (COI.RestrictL (toClass f) _ _ _ _)), H5. reflexivity.
Qed.

Proposition IsUnique : forall (r a b c f g:U),
  WellOrdering r c      ->
  Ordinal a             ->
  Ordinal b             ->
  Isom f (E a) r a c    ->
  Isom g (E b) r b c    ->
  a = b /\ f = g.
Proof.
  intros r a b c f g H1 H2 H3 H4 H5.
  apply COO.WhenSmallUnique with (toClass r) (toClass c); try assumption.
  - apply SetIsSmall.
  - apply COI.RestrictL, COI.EquivCompat2 with (toClass (E a)).
    1: apply SOE.ToClass. apply SOI.ToClass. assumption.
  - apply COI.RestrictL, COI.EquivCompat2 with (toClass (E b)).
    1: apply SOE.ToClass. apply SOI.ToClass. assumption.
Qed.

Proposition OrdinalSubset : forall (a b:U), Ordinal b ->
  a :<=: b -> exists c f, Ordinal c /\ c :<=: b /\ Isom f (E c) (E a) c a.
Proof.
  intros a b H1 H2.
  assert (Small (toClass a)) as G1. { apply Small.SetIsSmall. }
  assert (toClass a :<=: Ordinal) as G2. {
    intros c G2. apply Core.IsOrdinal with b. 1: assumption.
    apply H2. assumption. }
  assert (exists c, Ordinal c /\
    forall (f:U),
      f = (COS.RecurseSmallestFresh (toClass a) :|: c) ->
      COI.Isom (toClass f) COE.E COE.E (toClass c) (toClass a)) as H3. {
        apply COS.WhenSmall; assumption. }
  destruct H3 as [c [H3 H4]].
  remember (COS.RecurseSmallestFresh (toClass a) :|: c) as f eqn:H5.
  assert (f = f) as H6. { reflexivity. }
  specialize (H4 f H6). exists c, f.
  assert (Isom f (E c) (E a) c a) as H7. {
    apply SOI.FromClass.
    apply COI.EquivCompat2 with (COE.E :/: (toClass c)).
    + apply Equiv.Sym, SOE.ToClass.
    + apply COI.EquivCompat3 with (COE.E :/: (toClass a)).
      * apply Equiv.Sym, SOE.ToClass.
      * apply (COI.RestrictL _ COE.E), (COI.RestrictR _ _ COE.E). assumption. }
  assert(Monotone f) as H8. { apply (Monotone.FromIsom f c a); assumption. }
  assert (domain f = c) as G3. { apply H7. }
  assert (range f = a) as G4. { apply H7. }
  assert (c :<=: b) as H9. {
    intros d H9. apply Core.InclElemTran with f!d; try assumption.
    - apply Core.IsOrdinal with c; assumption.
    - apply H8. rewrite G4. apply Bij.IsInRange with c. 2: assumption. apply H7.
    - apply Monotone.IsIncl. 1: assumption. rewrite G3. assumption.
    - apply H2. apply Bij.IsInRange with c. 2: assumption. apply H7. }
  split. 1: assumption. split; assumption.
Qed.

