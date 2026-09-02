Require Import PeanoNat.
Import Init.Nat.

(* nat has more than 2 elements *)
Lemma L1 : ~ exists (x y:nat), forall (z:nat), z = x \/ z = y.
Proof.
    intro H. destruct H as [x H]. destruct H as [y H].
    remember (S (max x y)) as N eqn:E.
    remember (H N) as H' eqn:F. clear F H. destruct H' as [H|H];
    rewrite H in E. clear H.
 
Show.
