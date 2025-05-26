Require Import ZF.Class.Core.
Require Import ZF.Class.Inter2.
Require Import ZF.Class.Ordinal.Inf.
Require Import ZF.Set.Core.
Require Import ZF.Set.Empty.
Require Import ZF.Set.Inter.
Require Import ZF.Set.Incl.
Require Import ZF.Set.Ordinal.Core.
Require Import ZF.Set.Ordinal.Inter.
Require Import ZF.Set.Specify.

(* The infimum of the set a.                                                    *)
Definition inf (a:U) : U := :I( :{ a | Ordinal }: ).

Proposition Charac : forall (a x y:U),
  x :< inf a  ->
  y :< a      ->
  Ordinal y   ->
  x :< y.
Proof.
  intros a x y H1 H2 H3. apply Inter.Charac with :{a | Ordinal}:.
  1: assumption. apply Specify.Charac. split; assumption.
Qed.

Proposition CharacRev : forall (a x:U),
  :{a | Ordinal}:  <> :0:                   ->
  (forall y, y :< a -> Ordinal y -> x :< y) ->
  x :< inf a.
Proof.
  intros a x H1 H2. apply Inter.CharacRev. 1: assumption.
  intros y H3. apply Specify.Charac in H3. destruct H3 as [H3 H4].
  apply H2; assumption.
Qed.

(* The infimum of the class is the class of the infimum.                        *)
Proposition ToClass : forall (a:U),
  Class.Ordinal.Inf.inf (toClass a) :~: toClass (inf a).
Proof.
  intros a x. split; intros H1.
  - apply FromClass.Charac.
    apply Class.Inter.EquivCompat with (toClass a :/\: Ordinal). 2: assumption.
    intros y. split; intros H2.
    + apply Specify.Charac in H2. destruct H2 as [H2 H3]. split; assumption.
    + destruct H2 as [H2 H3]. apply Specify.Charac. split; assumption.
  - apply FromClass.Charac in H1.
    apply Class.Inter.EquivCompat with (toClass :{a|Ordinal}:). 2: assumption.
    intros y. split; intros H2.
    + destruct H2 as [H2 H3]. apply Specify.Charac. split; assumption.
    + apply Specify.Charac in H2. destruct H2 as [H2 H3]. split; assumption.
Qed.

(* The infimum of an ordinal is simply its intersection.                        *)
Proposition WhenOrdinal : forall (a:U), Ordinal a ->
  inf a = :I(a).
Proof.
  intros a H1. unfold inf.
  assert (:{a | Ordinal}: = a) as H2. {
    apply Specify.IsA. intros x H2. apply Core.IsOrdinal with a; assumption. }
  rewrite H2. reflexivity.
Qed.

Proposition IsZero : forall (a:U), Ordinal a ->
  inf a = :0:.
Proof.
  intros a H1. rewrite WhenOrdinal. 2: assumption.
  apply Inter.IsZero. assumption.
Qed.
