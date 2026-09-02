Require Import set.
Require Import Axiom_Skolem.
Require Import belong.
Require Import subset.
Require Import Axiom_Power_Set.
Require Import Axiom_Extensionality.

(* binary relation expression the fact that P(a) = b *)
Definition is_power_set (a b:set) : Prop :=
  forall x:set, x:b <-> subset x a.

Lemma power_set_is_unique : forall a:set, forall b c:set,
  is_power_set a b -> is_power_set a c -> b = c.
Proof.
  intros a b c Hab Hac. apply extensionality.
  unfold subset. intros x Hx. apply Hab in Hx. apply Hac in Hx. exact Hx.
  unfold subset. intros x Hx. apply Hac in Hx. apply Hab in Hx. exact Hx.
Qed.

(* Given a:set, the power set P(a) exists and is unique *)
(* The Skolem axiom allows us to extract an element for it, *) 
(* as well as a proof of the fact this element is indeed P(a) *)

Definition power (a:set) : set :=
  proj1_sig(skolem (power_set a) (power_set_is_unique a)).

Notation "'P' ( a )" := (power a) : core_scope.

Proposition power_is_power: forall a:set,
  forall x:set, x:P(a) <-> subset x a.
Proof.
  intros a. exact (proj2_sig (skolem (power_set a) (power_set_is_unique a))).
Qed.

Proposition power_intro: forall a x:set,
  subset x a -> x:P(a).
Proof.
  intros a x H. apply power_is_power. exact H.
Qed.

Proposition power_elim: forall a x:set,
  x:P(a) -> subset x a.
Proof.
  intros a x H. apply power_is_power. exact H.
Qed.


