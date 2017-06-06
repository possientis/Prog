Require Import set.
Require Import belong.
Require Import subset.
Require Import Axiom_Extensionality.
Require Import Axiom_Skolem.
Require Import Axiom_Empty_Set.



Definition empty(a:set): Prop := forall x:set, ~ belong x a.

Lemma empty_set_is_unique : forall x y:set,
  empty x -> empty y -> x = y.
Proof.
  intros x y Hx Hy. apply extensionality. 
  unfold subset. intros z Hz. unfold empty in Hx. 
  apply False_ind. apply (Hx z). exact Hz.
  unfold subset. intros z Hz. unfold empty in Hy.
  apply False_ind. apply (Hy z). exact Hz.
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


