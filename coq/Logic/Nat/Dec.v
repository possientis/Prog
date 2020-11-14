Require Import Le.

Require Import Logic.Class.Eq.
Require Import Logic.Class.Ord.

Require Import Logic.Axiom.Dec.

Require Import Logic.Nat.Leq.
Require Import Logic.Nat.Ord.

(*
Lemma boundedDec : forall (p:nat -> Prop), pDec p -> 
    forall (n:nat), Dec (exists (m:nat), p m /\ m <= n).
Proof.
    intros p H1. induction n as [|n IH].
    - destruct (H1 0) as [H2|H2].
        + left. exists 0. split; try assumption. apply le_n.
        + right. intros [m [H3 H4]]. apply le_0 in H4. subst.
          apply H2 in H3. contradiction.
    - destruct IH as [H2|H2].


Show.
*)
