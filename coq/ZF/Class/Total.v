Require Import ZF.Class.
Require Import ZF.Class.Incl.
Require Import ZF.Set.
Require Import ZF.Set.OrdPair.

(* Predicate expressing the fact that R is a total class on A.                  *)
Definition Total (R A:Class) : Prop := forall (x y:U), A x -> A y ->
  x = y \/ R :(x,y): \/ R :(y,x):.

Proposition TotalIncl : forall (R A B:Class),
  Total R A -> B :<=: A -> Total R B.
Proof.
  intros R A B H1 H2 x y H3 H4. apply H1; apply H2; assumption.
Qed.
