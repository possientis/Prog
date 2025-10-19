Require Import ZF.Class.Equiv.
Require Import ZF.Class.Order.E.
Require Import ZF.Class.Order.Isom.
Require Import ZF.Class.Order.Restrict.
Require Import ZF.Class.Order.WellOrdering.
Require Import ZF.Class.Ordinal.Order.
Require Import ZF.Class.Small.
Require Import ZF.Set.Core.
Require Import ZF.Set.Order.Isom.
Require Import ZF.Set.Order.RestrictOfClass.
Require Import ZF.Set.Order.WellOrdering.
Require Import ZF.Set.Ordinal.Core.
Require Import ZF.Set.Relation.RestrictOfClass.

Module COI := ZF.Class.Order.Isom.
Module COW := ZF.Class.Order.WellOrdering.
Module COO := ZF.Class.Ordinal.Order.

Module SOI := ZF.Set.Order.Isom.
Module SOW := ZF.Set.Order.WellOrdering.

Proposition IsIsom : forall (r b:U),
  WellOrdering r b          ->

  exists f a,
    Ordinal a               /\
    Isom f (E:/:a) r a b.
Proof.
  intros r b H1.
  assert (COW.WellOrdering (toClass r) (toClass b)) as H2. { assumption. }
  assert (Small (toClass b)) as H3. { apply SetIsSmall. }
  assert (exists a, Ordinal a /\ forall (g:U),
    g = (RecurseSmallestFresh (toClass r) (toClass b) :|: a) ->
    COI.Isom (toClass g) E (toClass r) (toClass a) (toClass b)) as H4. {
      apply COO.WhenSmall; assumption. }
  destruct H4 as [a [H4 H5]].
  remember (RecurseSmallestFresh (toClass r) (toClass b) :|: a) as f eqn:H6.
  exists f. exists a. split. 1: assumption. apply SOI.ToClass.
  apply COI.EquivCompat2 with (E:/:toClass a).
  - apply Equiv.Sym, RestrictOfClass.ToClass.
  - apply (proj1 (COI.RestrictL (toClass f) _ _ _ _)), H5. reflexivity.
Qed.

Proposition IsUnique : forall (r a b c f g:U),
  WellOrdering r c      ->
  Ordinal a             ->
  Ordinal b             ->
  Isom f (E:/:a) r a c  ->
  Isom g (E:/:b) r b c  ->
  a = b /\ f = g.
Proof.
  intros r a b c f g H1 H2 H3 H4 H5.
  apply COO.WhenSmallUnique with (toClass r) (toClass c); try assumption.
  - apply SetIsSmall.
  - apply COI.RestrictL, COI.EquivCompat2 with (toClass (E:/:a)).
    1: apply RestrictOfClass.ToClass. apply SOI.ToClass. assumption.
  - apply COI.RestrictL, COI.EquivCompat2 with (toClass (E:/:b)).
    1: apply RestrictOfClass.ToClass. apply SOI.ToClass. assumption.
Qed.
