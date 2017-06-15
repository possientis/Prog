Require Import set.
Require Import belong.
Require Import subset.
Require Import Axiom_Extensionality.
Require Import Axiom_Skolem.
Require Import Axiom_Empty_Set.



Definition empty(a:set): Prop := forall x:set, ~x:a.

Lemma empty_set_is_unique : forall a b:set,
  empty a -> empty b -> a = b.
Proof.
  intros a b Ha Hb. apply extensionality.
  unfold subset. intros x Hx. apply Ha in Hx. apply False_ind. exact Hx.
  unfold subset. intros x Hx. apply Hb in Hx. apply False_ind. exact Hx.
Qed.

(* We have an axiom which guarantees the existence of an empty set, while
 * the extensionality axiom allowed us to prove that such empty set was unique.
 * The 'empty' predicate therefore satisfies the assumptions of the skolem
 * axiom, which allows us to obtain an 'empty' set 'O'.
 *)


Definition O : set := proj1_sig (skolem empty_set_exists empty_set_is_unique).

Proposition empty_O : empty O.
Proof.
  exact (proj2_sig (skolem empty_set_exists empty_set_is_unique)). 
Qed.

Proposition empty_a_O : forall a:set,
  empty a <-> a = O.
Proof.
  intros a. split.
  intro Ha. apply empty_set_is_unique. exact Ha. apply empty_O.
  intro Ha. rewrite Ha. apply empty_O.
Qed.


