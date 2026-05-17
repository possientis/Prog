Require Import ZF.Class.Equiv.
Require Import ZF.Set.Core.
Require Import ZF.Set.Cardinal.Equiv.
Require Import ZF.Set.Diff.
Require Import ZF.Set.Empty.
Require Import ZF.Set.Incl.
Require Import ZF.Set.Ordinal.Core.
Require Import ZF.Set.Ordinal.Omega.
Require Import ZF.Set.Ordinal.Succ.
Require Import ZF.Set.Prod.
Require Import ZF.Set.Relation.Bij.
Require Import ZF.Set.Relation.Image.
Require Import ZF.Set.Relation.Restrict.
Require Import ZF.Set.Single.
Require Import ZF.Set.Union2.

Require Import ZF.Notation.Eval.


Module SCE := ZF.Set.Cardinal.Equiv.


(* A set is finite if and only if it is equipotent to a natural number.         *)
Definition Finite (a:U) : Prop := exists n, n :< :N /\ a :~: n.

(* Finiteness is preserved under equipotence.                                   *)
Proposition EquivCompat : forall (a b:U),
  a :~: b -> Finite a -> Finite b.
Proof.
  (* Proof by Claude.                                                           *)
  (* a is finite so a ~ n for some n in N. Since a ~ b, b ~ a ~ n.              *)
  intros a b H1 [n [H2 H3]]. exists n. split. 1: assumption.
  apply SCE.Tran with a. 2: assumption.
  apply SCE.Sym. assumption.
Qed.

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

Proposition WhenNat : forall (n:U), n :< :N -> Finite n.
Proof.
  intros n H1. exists n. split. 1: assumption. apply SCE.Refl.
Qed.

(* The empty set is finite.                                                     *)
Proposition Zero : Finite :0:.
Proof.
  (* Proof by Claude.                                                           *)
  (* The empty set is equipotent to 0, which is a natural number.               *)
  apply WhenNat. apply Omega.HasZero.
Qed.

(* A finite set remains finite after adjoining a single element.                *)
Proposition AddElem : forall (a b:U),
  Finite a -> Finite (a :\/: :{b}:).
Proof.
  (* Proof by Claude.                                                           *)
  (* Apply AddElem which gives a :\/: :{b}: = a or a :\/: :{b}: ~ succ a.       *)
  intros a b [n [H1 [f H2]]].
  assert (a :\/: :{b}: = a \/ a :\/: :{b}: :~: succ a) as H3. {
    apply SCE.AddElem. }
  destruct H3 as [H3|H3].
  - (* b is already in a, so a :\/: :{b}: = a and we are done.                  *)
    rewrite H3. exists n. split. 1: assumption. exists f. assumption.
  - (* b not in a: a :\/: :{b}: ~ succ a, so ~ succ n which is in N.            *)
    exists (succ n). split.
    + apply Omega.HasSucc. assumption.
    + apply SCE.Tran with (succ a). 1: assumption.
      apply SCE.SuccCompat. exists f. assumption.
Qed.

(* Removing an element from a finite set leaves a finite set.                   *)
Proposition SubElem : forall (a b:U),
  Finite a -> Finite (a :\: :{b}:).
Proof.
  (* Proof by Claude.                                                           *)
  (* a :\: :{b}: is a subset of a, hence finite.                                *)
  intros a b H1. apply InclCompat with a. 2: assumption. apply Diff.IsIncl.
Qed.

(* The product of a singleton and a finite set is finite.                       *)
Proposition ProdSingleL : forall (a b:U),
  Finite a -> Finite (:{b}: :x: a).
Proof.
  (* Proof by Claude.                                                           *)
  (* {b} x a ~ a, so finiteness transfers from a to {b} x a.                    *)
  intros a b H1. apply EquivCompat with a. 2: assumption.
  apply SCE.Sym. apply SCE.ProdSingleL.
Qed.

(* The product of a finite set and a singleton is finite.                       *)
Proposition ProdSingleR : forall (a b:U),
  Finite a -> Finite (a :x: :{b}:).
Proof.
  (* Proof by Claude.                                                           *)
  (* a x {b} ~ a, so finiteness transfers from a to a x {b}.                    *)
  intros a b H1. apply EquivCompat with a. 2: assumption.
  apply SCE.Sym. apply SCE.ProdSingleR.
Qed.

