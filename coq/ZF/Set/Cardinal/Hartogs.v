Require Import ZF.Class.Cardinal.Hartogs.
Require Import ZF.Class.Equiv.
Require Import ZF.Class.Incl.
Require Import ZF.Set.Core.
Require Import ZF.Set.FromClass.
Require Import ZF.Set.Ordinal.Core.
Require Import ZF.Set.Ordinal.Transitive.
Require Import ZF.Set.Relation.Inj.
Require Import ZF.Set.Relation.Restrict.


Module CCH := ZF.Class.Cardinal.Hartogs.

Definition hartogs (a:U) : U := fromClass (CCH.hartogs a) (CCH.IsSmall a).

Proposition ToClass : forall (a:U),
  toClass (hartogs a) :~: CCH.hartogs a.
Proof.
  intros a. apply FromClass.ToClass.
Qed.

Proposition Charac : forall (a x:U),
  x :< hartogs a <-> Ordinal x /\ exists f, Inj f x a.
Proof.
  intros a x. apply FromClass.Charac.
Qed.

Proposition IsIncl : forall (a:U),
  toClass (hartogs a) :<=: Ordinal.
Proof.
  intros a x H1. apply Charac in H1. apply H1.
Qed.

Proposition IsTransitive : forall (a:U),
  Transitive (hartogs a).
Proof.
  intros a c b H1 H2. apply Charac in H2. destruct H2 as [H2 [f H3]].
  assert (Ordinal c) as H4. { apply Core.IsOrdinal with b; assumption. }
  assert (Inj (f:|:c) c a) as H5. {
    apply Inj.Restrict with b. 1: assumption.
    apply Core.ElemIsIncl; assumption. }
  apply Charac. split. 1: assumption. exists (f:|:c). assumption.
Qed.

Proposition IsOrdinal : forall (a:U), Ordinal (hartogs a).
Proof.
  intro a. apply Core.WhenTransitive.
  - apply IsTransitive.
  - apply IsIncl.
Qed.



