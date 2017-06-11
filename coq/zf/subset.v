Require Import set.
Require Import belong.

(************************************************************************)
(*                The inclusion relation on sets                        *)
(************************************************************************)

Definition subset(a b:set) : Prop :=
  forall x:set, x:a -> x:b.

Proposition subset_refl : forall a:set, subset a a.
Proof.
  intros a. unfold subset. intros x H. exact H.
Qed.

Proposition subset_trans: forall a b c:set, 
  subset a b -> subset b c -> subset a c.
Proof.
  intros a b c Hab Hbc. unfold subset. intros x Hxa.
  unfold subset in Hab. unfold subset in Hbc.
  apply Hbc. apply Hab. exact Hxa.
Qed.


