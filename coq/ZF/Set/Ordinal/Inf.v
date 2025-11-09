Require Import ZF.Class.Equiv.
Require Import ZF.Class.Inter.
Require Import ZF.Class.Inter2.
Require Import ZF.Class.Ordinal.Inf.
Require Import ZF.Set.Core.
Require Import ZF.Set.Empty.
Require Import ZF.Set.Foundation.
Require Import ZF.Set.Inter.
Require Import ZF.Set.Incl.
Require Import ZF.Set.Ordinal.Core.
Require Import ZF.Set.Ordinal.Inter.
Require Import ZF.Set.Specify.

Module CIN := ZF.Class.Inter.
Module COI := ZF.Class.Ordinal.Inf.
Module SIN := ZF.Set.Inter.
Module SOI := ZF.Set.Ordinal.Inter.

(* The infimum of the set a.                                                    *)
Definition inf (a:U) : U := :I( :{ a | Ordinal }: ).

Proposition Charac : forall (a x y:U),
  x :< inf a  ->
  y :< a      ->
  Ordinal y   ->
  x :< y.
Proof.
  intros a x y H1 H2 H3. apply SIN.Charac with :{a | Ordinal}:.
  1: assumption. apply Specify.Charac. split; assumption.
Qed.

Proposition CharacRev : forall (a x:U),
  :{a | Ordinal}:  <> :0:                   ->
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
    apply CIN.EquivCompat with (toClass :{a|Ordinal}:). 2: assumption.
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
