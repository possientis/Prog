Require Import ZF.Class.Equiv.
Require Import ZF.Set.Core.
Require Import ZF.Set.Cardinal.Equiv.
Require Import ZF.Set.Incl.
Require Import ZF.Set.Ordinal.Core.
Require Import ZF.Set.Ordinal.Omega.
Require Import ZF.Set.Relation.Bij.
Require Import ZF.Set.Relation.Image.
Require Import ZF.Set.Relation.Restrict.

Require Import ZF.Notation.Eval.


Module SCE := ZF.Set.Cardinal.Equiv.


(* The class of finite sets, those equipotent to some natural number.           *)
Definition Finite : Class := fun a =>
  exists n, n :< :N /\ a :~: n.

Proposition InclCompat : forall (a b:U),
  a :<=: b -> Finite b -> Finite a.
Proof.
  intros a b H1 [n [H2 [f H3]]].
  assert (Ordinal n) as G1. { apply Omega.HasOrdinals. assumption. }
  assert (Ordinal :N) as G2. { apply Omega.IsOrdinal. }
  assert (a :~: f:[a]:) as H4. {
    exists (f:|:a). apply Bij.Restrict with b n; assumption. }
  assert (f:[a]: :<=: n) as H5. {
    intros y H5. apply (Bij.ImageCharac f b n) in H5. 2: assumption.
    destruct H5 as [x [H5 [H6 H7]]]. rewrite <- H7.
    apply Bij.IsInRange with b; assumption. }
  assert (exists m, Ordinal m /\ m :<=: n /\ f:[a]: :~: m) as H8. {
    apply SCE.OrdinalSubset; assumption. }
  destruct H8 as [m [H8 [H9 H10]]].
  assert (m :< :N) as H11. { apply Core.InclElemTran with n; assumption. }
  assert (a :~: m) as H12. { apply SCE.Tran with f:[a]:; assumption. }
  exists m; split; assumption.
Qed.
