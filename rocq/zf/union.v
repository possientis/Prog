Require Import set.
Require Import Axiom_Skolem.
Require Import belong.
Require Import Axiom_Union.
Require Import subset.
Require Import Axiom_Extensionality.
Require Import empty.
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

Proposition union_left : forall a b:set, subset a (union a b).
Proof.
  intros a b. unfold subset. intros x Hx. unfold union.
  apply union_intro with (y:= a). exact Hx. apply pair_left.
Qed.

Proposition union_right : forall a b:set, subset b (union a b).
Proof.
  intros a b. unfold subset. intros x Hx. unfold union.
  apply union_intro with (y:= b). exact Hx. apply pair_right.
Qed.

Proposition union_elim2 : forall a b x:set,
  x:(union a b) <-> x:a \/ x:b.
Proof.
  intros a b x. split.
  intro Hx. apply union_elim in Hx. elim Hx. 
  clear Hx. intros y H. elim H.
  clear H. intros Hx Hy. apply pair_elim in Hy. elim Hy.
  clear Hy. intro Hy. left. rewrite <- Hy. exact Hx.
  clear Hy. intro Hy. right. rewrite <- Hy. exact Hx. 
  intros H. elim H. 
  clear H. intros Hx. apply union_left. exact Hx.
  clear H. intros Hx. apply union_right. exact Hx.
Qed.

Proposition union_comm : forall a b:set, union a b = union b a.
Proof.
  intros a b. apply extensionality. 
  unfold subset. intros x Hx. apply union_elim2.
  apply union_elim2 in Hx. elim Hx.
  clear Hx. intro Hx. right. exact Hx.
  clear Hx. intro Hx. left. exact Hx.
  unfold subset. intros x Hx. apply union_elim2.
  apply union_elim2 in Hx. elim Hx.
  clear Hx. intro Hx. right. exact Hx.
  clear Hx. intro Hx. left. exact Hx.
Qed.

Proposition union_O_a : forall a:set, union O a = a.
Proof.
  intros a. apply extensionality.
  unfold subset. intros x Hx. apply union_elim2 in Hx. elim Hx.
  clear Hx. intro Hx. apply False_ind. apply empty_O in Hx. exact Hx.
  clear Hx. intro Hx. exact Hx.
  apply union_right.
Qed.


