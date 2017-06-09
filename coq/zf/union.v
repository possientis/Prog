Require Import set.
Require Import Axiom_Skolem.
Require Import belong.
Require Import Axiom_Union.
Require Import subset.
Require Import Axiom_Extensionality.
Require Import pair.


(* binary relation expressing the fact that Ua = b *)
Definition is_union (a b:set) : Prop :=
  forall x:set, x:b <-> exists y:set, x:y /\ y:a.

Lemma union_is_unique : forall a:set, forall b c:set,
  is_union a b -> is_union a c -> b = c.
Proof.
  intros a b c Hab Hac. apply extensionality.
  unfold subset. intros x Hx. apply Hab in Hx. apply Hac in Hx. exact Hx.
  unfold subset. intros x Hx. apply Hac in Hx. apply Hab in Hx. exact Hx.
Qed.

(* Given a:set, the union Ua exists and is unique *)
(* The Skolem axiom allows us to extract an element for it, *) 
(* as well as a proof of the fact this element is indeed Ua *)

Definition U (a:set) : set :=
  proj1_sig(skolem (union_axiom a) (union_is_unique a)).

(* U a is U a *)
Proposition union_is_union : forall a:set,
  forall x:set, x:(U a) <-> exists y:set, x:y /\ y:a.
Proof.
  intros a. exact (proj2_sig (skolem (union_axiom a) (union_is_unique a))).
Qed.

Proposition union_intro : forall a x y:set,
  x:y -> y:a  -> x:(U a).
Proof.
  intros a x y Hxy Hya. apply union_is_union. 
  exists y. split. exact Hxy. exact Hya.
Qed.

Proposition union_elim : forall a x:set,
  x:(U a) -> exists y:set, x:y /\ y:a.
Proof.
  intros a x H. apply union_is_union. exact H.
Qed.

(* We are now defining the binary union operator on sets *)
Definition union (a b:set) : set := U {a,b}.



