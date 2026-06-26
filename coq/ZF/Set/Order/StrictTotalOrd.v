Require Import ZF.Class.Equiv.
Require Import ZF.Class.Order.StrictTotalOrd.
Require Import ZF.Set.Core.
Require Import ZF.Set.Incl.
Require Import ZF.Set.Order.StrictOrd.
Require Import ZF.Set.Order.Total.
Require Import ZF.Set.OrdPair.

Module COS := ZF.Class.Order.StrictTotalOrd.

(* Predicate expressing the fact that r is a strict total order set on a.       *)
Definition StrictTotalOrd (r a:U) : Prop := StrictOrd r a /\ Total r a.

(* Strict total order on a restricts to strict total order on any subset b.     *)
Proposition InclCompat : forall (r a b:U),
  b :<=: a -> StrictTotalOrd r a -> StrictTotalOrd r b.
Proof.
  (* Proof by Hermes + gpt 5.5                                                  *)
  (* Both components restrict separately to the subset b.                       *)
  intros r a b H1 [H2 H3]. split.
  - apply StrictOrd.InclCompat with a; assumption.
  - apply Total.InclCompat with a; assumption.
Qed.
