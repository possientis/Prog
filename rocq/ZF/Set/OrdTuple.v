Declare Scope ZF_Set_OrdTuple_scope.
Open    Scope ZF_Set_OrdTuple_scope.

Require Import ZF.Set.Core.
Require Import ZF.Set.OrdPair.

Definition ordTuple3 (a1 a2 a3:U) : U := :( :(a1,a2): , a3 ):.

Notation ":( a , b , c ):" := (ordTuple3 a b c)
  (at level 1, no associativity) : ZF_Set_OrdTuple_scope.

Definition ordTuple4 (a1 a2 a3 a4:U) : U := :( :(a1,a2,a3): , a4 ):.

Notation ":( a , b , c , d ):" := (ordTuple4 a b c d)
  (at level 1, no associativity) : ZF_Set_OrdTuple_scope.

(* Equal ordered triples have equal components.                                 *)
Proposition Equal3 : forall (a1 a2 a3 b1 b2 b3:U),
  :(a1,a2,a3): = :(b1,b2,b3): -> a1 = b1 /\ a2 = b2 /\ a3 = b3.
Proof.
  intros a1 a2 a3 b1 b2 b3 H. apply OrdPair.Equal in H.
  destruct H as [H H3]. apply OrdPair.Equal in H. destruct H as [H1 H2].
  auto.
Qed.

(* Equal ordered 4-tuples have equal components.                                *)
Proposition Equal4 : forall (a1 a2 a3 a4 b1 b2 b3 b4:U),
  :(a1,a2,a3,a4): = :(b1,b2,b3,b4): -> a1 = b1 /\ a2 = b2 /\ a3 = b3 /\ a4 = b4.
Proof.
  intros a1 a2 a3 a4 b1 b2 b3 b4 H. apply OrdPair.Equal in H. destruct H as [H H4].
  apply Equal3 in H. destruct H as [H1 [H2 H3]].
  auto.
Qed.
