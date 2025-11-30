Require Import ZF.Axiom.Classic.
Require Import ZF.Class.Equiv.
Require Import ZF.Class.Inter.
Require Import ZF.Class.Inter2.
Require Import ZF.Class.Order.E.
Require Import ZF.Class.Ordinal.Inf.
Require Import ZF.Set.Core.
Require Import ZF.Set.Empty.
Require Import ZF.Set.Foundation.
Require Import ZF.Set.Inter.
Require Import ZF.Set.Incl.
Require Import ZF.Set.Order.Minimal.
Require Import ZF.Set.Order.RestrictOfClass.
Require Import ZF.Set.Ordinal.Core.
Require Import ZF.Set.Ordinal.Inter.
Require Import ZF.Set.OrdPair.
Require Import ZF.Set.Specify.

Module CIN := ZF.Class.Inter.
Module COI := ZF.Class.Ordinal.Inf.
Module SIN := ZF.Set.Inter.
Module SOI := ZF.Set.Ordinal.Inter.

(* The infimum of the set a.                                                    *)
Definition inf (a:U) : U := :I( {{ x :< a | Ordinal }} ).

Proposition Charac : forall (a x y:U),
  x :< inf a  ->
  y :< a      ->
  Ordinal y   ->
  x :< y.
Proof.
  intros a x y H1 H2 H3. apply SIN.Charac with {{ x :< a | Ordinal }}.
  1: assumption. apply Specify.Charac. split; assumption.
Qed.

Proposition CharacRev : forall (a x:U),
  {{ x:< a | Ordinal }}  <> :0:             ->
  (forall y, y :< a -> Ordinal y -> x :< y) ->
  x :< inf a.
Proof.
  intros a x H1 H2. apply SIN.CharacRev. 1: assumption.
  intros y H3. apply Specify.Charac in H3. destruct H3 as [H3 H4].
  apply H2; assumption.
Qed.

(* The infimum of the class is the class of the infimum.                        *)
Proposition ToClass : forall (a:U),
  toClass (inf a) :~: COI.inf (toClass a).
Proof.
  intros a x. split; intros H1.
 - apply FromClass.Charac in H1.
    apply CIN.EquivCompat with (toClass {{ x :< a | Ordinal }}). 2: assumption.
    intros y. split; intros H2.
    + destruct H2 as [H2 H3]. apply Specify.Charac. split; assumption.
    + apply Specify.Charac in H2. destruct H2 as [H2 H3]. split; assumption.
  - apply FromClass.Charac.
    apply CIN.EquivCompat with (toClass a :/\: Ordinal). 2: assumption.
    intros y. split; intros H2.
    + apply Specify.Charac in H2. destruct H2 as [H2 H3]. split; assumption.
    + destruct H2 as [H2 H3]. apply Specify.Charac. split; assumption.
Qed.

Proposition WhenOrdinals : forall (a:U),
  toClass a :<=: Ordinal -> inf a = :I(a).
Proof.
  intros a H1. apply Specify.IsA in H1. unfold inf. rewrite H1. reflexivity.
Qed.

Proposition WhenEmpty : inf :0: = :0:.
Proof.
  rewrite WhenOrdinals.
  - apply SIN.WhenEmpty.
  - intros x H1. apply Empty.Charac in H1. contradiction.
Qed.

Proposition IsOrdinal : forall (a:U), Ordinal (inf a).
Proof.
  intros a. apply SOI.IsOrdinal. intros x H1.
  apply Specify.IsInP in H1. assumption.
Qed.

Proposition IsLowerBound : forall (a b:U),
  toClass a :<=: Ordinal ->
  b :< a                 ->
  inf a :<=: b.
Proof.
  intros a b H1 H2. rewrite WhenOrdinals. 2: assumption.
  apply SOI.IsLowerBound; assumption.
Qed.

Proposition IsLargest : forall (a b:U),
  toClass a :<=: Ordinal          ->
  a <> :0:                        ->
  (forall c, c :< a -> b :<=: c)  ->
  b :<=: inf a.
Proof.
  intros a b H1 H2 H3. rewrite WhenOrdinals. 2: assumption.
  apply SOI.IsLargest; assumption.
Qed.

Proposition Contradict : forall (a b:U),
  toClass a :<=: Ordinal ->
  Ordinal b              ->
  b :< a                 ->
  b :< inf a             ->
  False.
Proof.
  intros a b H1 H2 H3 H4.
  assert (inf a :<=: b) as H5. { apply IsLowerBound; assumption. }
  assert (b :< b) as H6. { apply H5. assumption. }
  revert H6. apply NoElemLoop1.
Qed.

Proposition IsMinimal : forall (a:U),
  toClass a :<=: Ordinal      ->
  a <> :0:                    ->
  Minimal (E:/:a) a (inf a).
Proof.
  intros a H1 H2.
  assert (exists b,
    Ordinal b                   /\
    b :< a                      /\
    forall c , c :< a -> b :<=: c) as H3. {
      apply Core.HasMinimal. 1: assumption.
      apply Empty.NotEmptyToClass. assumption. }
  destruct H3 as [b [H3 [H4 H5]]].
  assert (Minimal (E:/:a) a b) as H6. {
    split. 1: assumption.
    intros c H6 H7.
    assert (Ordinal c) as H8. { apply H1. assumption. }
    apply RestrictOfClass.Charac2 in H7. destruct H7 as [H7 [H9 H10]].
    apply E.Charac2 in H10.
    assert (c :< c) as H11. { apply H5; assumption. }
    revert H11. apply NoElemLoop1. }
  assert (Ordinal (inf a)) as H7. { apply IsOrdinal. }
  assert (inf a = b) as H8. {
    apply DoubleInclusion. split.
    - apply IsLowerBound; assumption.
    - apply IsLargest; assumption. }
  rewrite H8. assumption.
Qed.

Proposition IsIn : forall (a:U),
  toClass a :<=: Ordinal ->
  a <> :0:               ->
  inf a :< a.
Proof.
  intros a H1 H2.
  assert (Minimal (E:/:a) a (inf a)) as H3. { apply IsMinimal; assumption. }
  apply H3.
Qed.

Proposition WhenMore : forall (a b:U),
  toClass a :<=: Ordinal                    ->
  a <> :0:                                  ->
  Ordinal b                                 ->
  inf a :< b                                ->
  exists c, Ordinal c /\ c :< a /\ c :< b.
Proof.
  intros a b H1 H2 H3 H4.
  apply NotForAllNot. intros H5.
  assert (forall x, x :< a -> b :<=: x) as H6. {
    intros c H6.
    assert (Ordinal c) as H7. { apply H1. assumption. }
    assert (c :< b \/ b :<=: c) as H8. { apply Core.ElemOrIncl; assumption. }
    destruct H8 as [H8|H8]. 2: assumption. exfalso.
    apply H5 with c. split. 1: assumption. split; assumption. }
  assert (b :<=: inf a) as H7. { apply IsLargest; assumption. }
  assert (inf a :< inf a) as H8. { apply H7. assumption. }
  revert H8. apply NoElemLoop1.
Qed.
