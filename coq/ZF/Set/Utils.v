Require Import ZF.Axiom.Core.
Require Import ZF.Set.Empty.
Require Import ZF.Set.Include.
Require Import ZF.Set.OrdPair.
Require Import ZF.Set.Pair.
Require Import ZF.Set.Singleton.

(* The empty set is not an ordered pair                                         *)
Proposition EmptyNotOrdPair : forall (x y:U), ~ :0: = :(x,y):.
Proof.
  intros x y H1. apply DoubleInclusion in H1. destruct H1 as [_ H1].
  apply EmptySetEmpty with :{x}:. apply H1, PairIn1.
Qed.
