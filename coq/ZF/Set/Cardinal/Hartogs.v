Require Import ZF.Axiom.Classic.
Require Import ZF.Class.Cardinal.Hartogs.
Require Import ZF.Class.Equiv.
Require Import ZF.Class.Incl.
Require Import ZF.Set.Cardinal.Core.
Require Import ZF.Set.Core.
Require Import ZF.Set.Empty.
Require Import ZF.Set.FromClass.
Require Import ZF.Set.Ordinal.Core.
Require Import ZF.Set.Ordinal.Transitive.
Require Import ZF.Set.Relation.Compose.
Require Import ZF.Set.Relation.Inj.
Require Import ZF.Set.Relation.Restrict.


Module CCH := ZF.Class.Cardinal.Hartogs.
Module SCC := ZF.Set.Cardinal.Core.
Module SOC := ZF.Set.Ordinal.Core.

Definition hartogs (a:U) : U := fromClass (CCH.hartogs a) (CCH.IsSmall a).

(* hartogs(a) as a class equals the class-level Hartogs number of a.            *)
Proposition ToClass : forall (a:U),
  toClass (hartogs a) :~: CCH.hartogs a.
Proof.
  intros a. apply FromClass.ToClass.
Qed.

(* x is in hartogs(a) iff x is an ordinal admitting an injection into a.        *)
Proposition Charac : forall (a x:U),
  x :< hartogs a <-> Ordinal x /\ exists f, Inj f x a.
Proof.
  intros a x. apply FromClass.Charac.
Qed.

(* Every element of hartogs(a) is an ordinal.                                   *)
Proposition IsIncl : forall (a:U),
  toClass (hartogs a) :<=: Ordinal.
Proof.
  intros a x H1. apply Charac in H1. apply H1.
Qed.

(* hartogs(a) is a transitive set.                                              *)
Proposition IsTransitive : forall (a:U),
  Transitive (hartogs a).
Proof.
  intros a c b H1 H2. apply Charac in H2. destruct H2 as [H2 [f H3]].
  assert (Ordinal c) as H4. { apply SOC.IsOrdinal with b; assumption. }
  assert (Inj (f:|:c) c a) as H5. {
    apply Inj.Restrict with b. 1: assumption.
    apply SOC.ElemIsIncl; assumption. }
  apply Charac. split. 1: assumption. exists (f:|:c). assumption.
Qed.

(* hartogs(a) is an ordinal.                                                    *)
Proposition IsOrdinal : forall (a:U), Ordinal (hartogs a).
Proof.
  intro a. apply SOC.WhenTransitive.
  - apply IsTransitive.
  - apply IsIncl.
Qed.

(* hartogs(a) is a cardinal number.                                             *)
Proposition IsCardinal : forall (a:U), Cardinal (hartogs a).
Proof.
  intros a. apply SCC.Charac. split. 1: apply IsOrdinal.
  intros b H1 H2.
  assert (Ordinal (hartogs a)) as G1. { apply IsOrdinal. }
  destruct H2 as [f H2].
  assert (b :< hartogs a \/ hartogs a :<=: b) as H3. {
    apply SOC.ElemOrIncl; assumption. }
  destruct H3 as [H3|H3]. 2: assumption. exfalso.
  apply Charac in H3. destruct H3 as [_ [g H3]].
  assert (Inj f (hartogs a) b) as H4. { apply Bij.IsInj. assumption. }
  assert (Inj (g :.: f) (hartogs a) a) as H5. {
    apply Inj.Compose with b; assumption. }
  assert (hartogs a :< hartogs a) as H6. {
    apply Charac. split. 1: assumption. exists (g :.: f). assumption. }
  revert H6. apply Foundation.NoLoop1.
Qed.

(* The empty set is an element of hartogs(a).                                   *)
Proposition HasZero : forall (a:U), :0: :< hartogs a.
Proof.
  intros a. apply Charac. split.
  - apply SOC.Zero.
  - exists :0:. apply Inj.WhenZero. reflexivity.
Qed.

(* The cardinal of a is strictly less than the Hartogs number of a.             *)
Proposition IsMore : forall (a:U), card a :< hartogs a.
Proof.
  intros a.
  assert (Ordinal (card a)) as H1. { apply SCC.IsOrdinal. }
  assert (Ordinal (hartogs a)) as H2. { apply IsOrdinal. }
  assert (card a = :0: \/ card a <> :0:) as H3. { apply LawExcludedMiddle. }
  destruct H3 as [H3|H3].
  - rewrite H3. apply HasZero.
  - assert (card a :< hartogs a \/ hartogs a :<=: card a) as H4. {
      apply SOC.ElemOrIncl; assumption. }
    destruct H4 as [H4|H4]. 1: assumption. exfalso.
    assert (card a :~: a) as H5. {
      apply Equiv.Sym, IsEquivNotZero. assumption. }
    destruct H5 as [f H5].
    assert (Inj f (card a) a) as H6. { apply Bij.IsInj. assumption. }
    assert (Inj (f:|:hartogs a) (hartogs a) a) as H7. {
      apply Inj.Restrict with (card a); assumption. }
    assert (hartogs a :< hartogs a) as H8. {
      apply Charac. split. 1: assumption. exists (f:|:hartogs a). assumption. }
    revert H8. apply Foundation.NoLoop1.
Qed.

(* There is no injection from hartogs(a) into a.                                *)
Proposition HasNoInj : forall (a:U), ~ exists f, Inj f (hartogs a) a.
Proof.
  intros a [f H1].
  assert (Ordinal (hartogs a)) as H2. { apply IsOrdinal. }
  assert (hartogs a :< hartogs a) as H3. {
    apply Charac. split. 1: assumption. exists f. assumption. }
  revert H3. apply Foundation.NoLoop1.
Qed.

