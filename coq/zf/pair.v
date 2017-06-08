Require Import set.
Require Import Axiom_Skolem.
Require Import belong.
Require Import Axiom_Pairing.
Require Import subset.
Require Import Axiom_Extensionality.

(* ternary relation expressing the fact that {a.b} == c *)
Definition pair_relation(a b c:set) : Prop :=
  forall x:set, belong x c <-> x = a \/ x = b. 

Lemma pair_is_unique: forall a b:set, forall c d:set,
  pair_relation a b c -> pair_relation a b d -> c = d.
Proof.
  intros a b c d Hc Hd. apply extensionality. 
  unfold subset. intros x Hx. apply Hc in Hx. apply Hd in Hx. exact Hx.
  unfold subset. intros x Hx. apply Hd in Hx. apply Hc in Hx. exact Hx.
Qed.

(* Given a b:set, the pair {a,b} exists and is unique *)
(* The Skolem axiom allows us to extract an element for it, *) 
(* as well as a proof of the fact this element is indeed {a,b} *)
Definition upair(a b:set) : set := 
  proj1_sig (skolem (pairing a b) (pair_is_unique a b)).

Notation "{ a , b }" := (upair a b) : core_scope.

(* pair a b = {a, b} *)
Proposition pair_is_pair : forall a b:set, 
  forall x:set, belong x {a,b} <-> x = a \/ x = b.
Proof.
  intros a b. exact (proj2_sig (skolem (pairing a b) (pair_is_unique a b))).
Qed.

(* a belongs to {a,b} *)
Proposition pair_left : forall a b:set, belong a {a,b}.
Proof.
  intros a b. apply pair_is_pair. left. reflexivity.
Qed.

(* b belongs to {a,b} *)
Proposition pair_right : forall a b:set, belong b {a,b}.
Proof.
  intros a b. apply pair_is_pair. right. reflexivity.
Qed.

(* x in {a,b} -> x = a \/ x = b *)
Proposition pair_elim : forall x a b:set, belong x {a,b} -> x = a \/ x = b.
Proof.
  intros x a b. apply pair_is_pair.
Qed.

(* not useful in general *)
Lemma pair_subset: forall a b:set, subset {a,b} {b,a}.
Proof.
  intros a b. unfold subset. intros x Hx. cut (x = a \/ x = b).
  intros H'. elim H'. 
  clear H'. intro H'. rewrite H'. apply pair_right.
  clear H'. intro H'. rewrite H'. apply pair_left.
  apply pair_elim. exact Hx.
Qed.

(* {a,b} = {b,a} *)
Proposition pair_commute : forall a b:set, {a,b} = {b,a}.
Proof.
  intros a b. apply extensionality. apply pair_subset. apply pair_subset. 
Qed.




