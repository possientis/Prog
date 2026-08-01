Require Import ZF.Class.Equiv.
Require Import ZF.Class.Cardinal.Aleph.
Require Import ZF.Class.Cardinal.InfiniteCard.
Require Import ZF.Set.Core.
Require Import ZF.Set.Empty.
Require Import ZF.Set.Ordinal.Ordinal.
Require Import ZF.Set.Ordinal.Omega.
Require Import ZF.Set.Ordinal.Character.
Require Import ZF.Set.Relation.EvalOfClass.

Require Import ZF.Notation.Eval.


(* The set a is a singular cardinal.                                            *)
Definition Singular (a:U) : Prop := InfiniteCard a /\ charac a :< a.

(* Aleph omega is a singular cardinal.                                          *)
Proposition WhenAlephN : Singular (Aleph!:N).
Proof.
  assert (Ordinal :N) as G1. { apply Omega.IsOrdinal. }
  assert (Ordinal :0:) as G2. { apply Ordinal.Zero. }
  assert (InfiniteCard Aleph!:N) as H1. {
    apply Aleph.IsInfiniteCard. assumption. }
  assert (Aleph!:0: :< Aleph!:N) as H2. {
    apply Aleph.ElemCompat; try assumption. apply Omega.HasZero. }
  assert (:N :< Aleph! :N) as H3. {
    rewrite Aleph.WhenZero in H2. assumption. }
  assert (charac Aleph!:N = :N) as H4. { apply Character.WhenAlephN. }
  assert (charac Aleph!:N :< Aleph!:N) as H5. { rewrite H4. assumption. }
  split; assumption.
Qed.
