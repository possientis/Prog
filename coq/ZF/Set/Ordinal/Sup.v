Require Import ZF.Class.Incl.
Require Import ZF.Class.Equiv.
Require Import ZF.Class.Ordinal.Sup.
Require Import ZF.Set.Core.
Require Import ZF.Set.Empty.
Require Import ZF.Set.Ordinal.Core.
Require Import ZF.Set.Ordinal.Union.
Require Import ZF.Set.Specify.
Require Import ZF.Set.Union.

Module COS := ZF.Class.Ordinal.Sup.
Module SOU := ZF.Set.Ordinal.Union.

(* The supremum of the set a.                                                   *)
Definition sup (a:U) : U := :U( :{ a | Ordinal }: ).

Proposition Charac : forall (a:U),
  forall x, x :< sup a <-> exists y, x :< y /\ y :< a /\ Ordinal y.
Proof.
  intros a x. split; intros H1.
  - apply Union.Charac in H1. destruct H1 as [y [H1 H2]].
    apply Specify.Charac in H2. destruct H2 as [H2 H3].
    exists y. split. 1: assumption. split; assumption.
  - destruct H1 as [y [H1 [H2 H3]]]. apply Union.Charac.
    exists y. split. 1: assumption. apply Specify.Charac.
    split; assumption.
Qed.

(* The supremum of the class is the class of the supremum.                      *)
Proposition ToClass : forall (a:U),
   toClass (sup a) :~: COS.sup (toClass a).
Proof.
  intros a x. split; intros H1.
  - apply Charac in H1. destruct H1 as [y [H1 [H2 H3]]].
    exists y. split. 1: assumption. split; assumption.
  - destruct H1 as [y [H1 [H2 H3]]]. apply Charac. exists y.
    split. 1: assumption. split; assumption.
Qed.

Proposition WhenOrdinals : forall (a:U),
  toClass a :<=: Ordinal -> sup a = :U(a).
Proof.
  intros a H1. apply Specify.IsA in H1. unfold sup. rewrite H1. reflexivity.
Qed.

Proposition WhenEmpty : sup :0: = :0:.
Proof.
  rewrite WhenOrdinals.
  - apply Union.WhenEmpty.
  - intros x H1. apply Empty.Charac in H1. contradiction.
Qed.

(* The supremum of a set of ordinals is an ordinal.                             *)
Proposition IsOrdinal : forall (a:U),
  toClass a :<=: Ordinal -> Ordinal (sup a).
Proof.
  intros a H1. rewrite WhenOrdinals. 2: assumption.
  apply SOU.IsOrdinal. assumption.
Qed.

(* The supremum of a set of ordinals is an upper-bound of that set.             *)
Proposition IsUpperBound : forall (a b:U),
  toClass a :<=: Ordinal  ->
  b :< a                  ->
  b :<=: sup a.
Proof.
  intros a b H1 H2. rewrite WhenOrdinals. 2: assumption.
  apply SOU.IsUpperBound; assumption.
Qed.

Proposition IsSmallest : forall (a b:U),
  toClass a :<=: Ordinal          ->
  (forall c, c :< a -> c :<=: b)  ->
  sup a :<=: b.
Proof.
  intros a b H1 H2. rewrite WhenOrdinals. 2: assumption.
  apply SOU.IsSmallest; assumption.
Qed.
