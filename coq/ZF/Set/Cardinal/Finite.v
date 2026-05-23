Require Import ZF.Axiom.Choice.
Require Import ZF.Set.Cardinal.Core.
Require Import ZF.Set.Cardinal.Equiv.
Require Import ZF.Set.Core.
Require Import ZF.Set.Diff.
Require Import ZF.Set.Empty.
Require Import ZF.Set.Finite.
Require Import ZF.Set.Ordinal.Omega.
Require Import ZF.Set.Ordinal.Succ.
Require Import ZF.Set.Single.
Require Import ZF.Set.Union2.
Require Import ZF.Notation.Equiv.
Require Import ZF.Notation.Lt.
Require Import ZF.Notation.Union.

Module SCC := ZF.Set.Cardinal.Core.
Module SCE := ZF.Set.Cardinal.Equiv.
Module SFI := ZF.Set.Finite.

(* The cardinal of a finite set is a natural number.                            *)
Proposition CardIsNat : forall (a:U),
  Finite a -> card a :< :N.
Proof.
  (* Proof by Hermes.                                                           *)
  intros a [n [H1 H2]].
  (* A finite set is equipotent to some natural number n.                       *)
  assert (card a = card n) as H3. { apply SCC.WhenEquiv. assumption. }
  (* Natural numbers are their own cardinals.                                   *)
  assert (card n = n) as H4. { apply SCC.WhenNat. assumption. }
  rewrite H3, H4. assumption.
Qed.

(* Assuming choice, a set whose cardinal is natural is finite.                  *)
Proposition WhenCardNat : forall (a:U), Choice ->
  card a :< :N -> Finite a.
Proof.
  (* Proof by Hermes.                                                           *)
  intros a AC H1. exists (card a). split. 1: assumption.
  (* Choice gives a bijection between a and its cardinal.                       *)
  apply SCC.IsEquivChoice. assumption.
Qed.

(* Adding a new element to a finite set increments its cardinal.                *)
Proposition AddNewElem : forall (a b:U),
  Finite a -> ~ b :< a -> card (a :\/: :{b}:) = succ (card a).
Proof.
  (* Proof by Hermes.                                                           *)
  intros a b H1 H2.
  (* A finite set is equipotent to an ordinal, hence to its cardinal.           *)
  assert (WithOrdinal a) as H3. {
    destruct H1 as [n [H1 H3]]. exists n. split. 2: assumption.
    apply Omega.HasOrdinals. assumption. }
  assert (a :~: card a) as H4. { apply SCC.IsEquivGen. assumption. }
  (* Since b is new, adjoining b gives a set equipotent to succ(a).             *)
  assert (a :\/: :{b}: :~: succ a) as H5. {
    assert (a :\/: :{b}: = a \/ a :\/: :{b}: :~: succ a) as [H5|H5]. {
      apply SCE.AddElem. } 2: assumption.
    exfalso. apply H2. rewrite <- H5. apply Union2.Charac.
    right. apply Single.IsIn. }
  (* Transporting the bijection a ~ card(a) through successor gives the size.   *)
  assert (succ a :~: succ (card a)) as H6. { apply SCE.SuccCompat. assumption. }
  assert (a :\/: :{b}: :~: succ (card a)) as H7. {
    apply SCE.Tran with (succ a); assumption. }
  assert (card (a :\/: :{b}:) = card (succ (card a))) as H8. {
    apply SCC.WhenEquiv. assumption. }
  assert (card a :< :N) as H9. { apply CardIsNat. assumption. }
  assert (succ (card a) :< :N) as H10. { apply Omega.HasSucc. assumption. }
  assert (card (succ (card a)) = succ (card a)) as H11. {
    apply SCC.WhenNat. assumption. }
  rewrite H8, H11. reflexivity.
Qed.

(* Removing an element from a set of cardinal succ(n) leaves cardinal n.        *)
Proposition RemoveElem : forall (n a b:U),
  n :< :N -> card a = succ n -> b :< a -> card (a :\: :{b}:) = n.
Proof.
  (* Proof by Hermes.                                                           *)
  intros n a b H1 H2 H3.
  remember (a :\: :{b}:) as c eqn:H4.
  (* Since card(a) is a successor, a is equipotent to its cardinal.             *)
  assert (card a <> :0:) as H5. { rewrite H2. apply Succ.NotZero. }
  assert (a :~: card a) as H6. { apply SCC.IsEquivNotZero. assumption. }
  (* Thus a is finite, being equipotent to the natural number succ(n).          *)
  assert (Finite a) as H7. {
    exists (succ n). split.
    - apply Omega.HasSucc. assumption.
    - rewrite <- H2. assumption. }
  assert (Finite c) as H8. { rewrite H4. apply SFI.SubElem. assumption. }
  (* The removed element is not in the remaining set.                           *)
  assert (~ b :< c) as H9. {
    rewrite H4. intros H9. apply Diff.Charac in H9.
    destruct H9 as [_ H9]. apply H9. apply Single.IsIn. }
  (* Adding the removed element back increments the remaining cardinal.         *)
  assert (card (c :\/: :{b}:) = succ (card c)) as H10. {
    apply AddNewElem; assumption. }
  assert (c :\/: :{b}: = a) as H11. {
    rewrite H4. apply Diff.RemoveAddElem. assumption. }
  rewrite H11, H2 in H10. apply Succ.Injective in H10.
  symmetry. assumption.
Qed.
