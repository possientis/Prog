Require Import set.
Require Import equiv.
Require Import equiv_symmetric.
Require Import equiv_transitive.

(* obvious consequence of transitivity and symmetry *)
Proposition equiv_compatible: forall (a a' b b':set),
  equiv a a' -> equiv b b' -> equiv a b -> equiv a' b'.
Proof.
  intros a a' b b' Haa' Hbb' Hab.
  apply equiv_transitive with (b:= b).
  apply equiv_transitive with (b:= a).
  apply equiv_symmetric. exact Haa'. exact Hab. exact Hbb'.
Qed.
