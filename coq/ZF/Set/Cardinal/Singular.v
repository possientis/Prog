Require Import ZF.Class.Equiv.
Require Import ZF.Class.Cardinal.Aleph.
Require Import ZF.Class.Cardinal.InfiniteCard.
Require Import ZF.Set.Core.
Require Import ZF.Set.Empty.
Require Import ZF.Set.Ordinal.Mult.
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

(* Every positive finite omega multiple indexes a singular aleph.               *)
Proposition WhenAlephNMultNat : forall (n:U),
  n :< :N                         ->
  :0: :< n                        ->
  Singular (Aleph! (:N :*: n)).
Proof.
(* Proof by Hermes + gpt 5.5                                                    *)
  intros n H1 H2.
  assert (Ordinal :0:) as G1. { apply Ordinal.Zero. }
  assert (Ordinal :N) as G2. { apply Omega.IsOrdinal. }
  assert (Ordinal n) as G3. { apply Omega.HasOrdinals. assumption. }
  assert (Ordinal (:N :*: n)) as G4. { apply Mult.IsOrdinal; assumption. }
  assert (:0: :< :N) as G5. { apply Omega.HasZero. }
  assert (InfiniteCard (Aleph! (:N :*: n))) as H3. {
    apply Aleph.IsInfiniteCard. assumption. }
  assert (:0: :< :N :*: n) as H4. { apply Mult.HasZero; assumption. }
  assert (Aleph!:0: :< Aleph! (:N :*: n)) as H5. {
    apply Aleph.ElemCompat; assumption. }
  assert (:N :< Aleph! (:N :*: n)) as H6. {
    rewrite Aleph.WhenZero in H5. assumption. }
  assert (charac (Aleph! (:N :*: n)) = :N) as H7. {
    apply Character.WhenAlephNMultNat; assumption. }
  assert (charac (Aleph! (:N :*: n)) :< Aleph! (:N :*: n)) as H8. {
    rewrite H7. assumption. }
  split; assumption.
Qed.
