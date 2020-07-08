(* Computational omni-science                                                   *)

Require Import provable.

Definition CO : Prop := exists (F:(nat -> bool) -> bool), forall (f:nat -> bool), 
    F f = true <->  exists (n:nat), f n = true.


Lemma L1 : CO -> LPO.
Proof.
    unfold CO, LPO. intros [F H] f. destruct (F f) eqn:E.
    - left. apply H. assumption.
    - right. intros H'. destruct (H f) as [H1 H2]. apply H2 in H'. 
      rewrite E in H'. inversion H'.
Qed.
