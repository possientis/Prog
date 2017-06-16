Require Import set.
Require Import belong.
Require Import subset.
Require Import Axiom_Extensionality.
Require Import empty.
Require Import pair.

(************************************************************************)
(*                          singleton sets                              *)
(************************************************************************)

Definition singleton (x:set) : set := {x,x}.

Proposition singleton_belong: forall x y:set, x:(singleton y) <-> x = y.
Proof.
  intros x y. split. intros Hxy. unfold singleton in Hxy.
  apply pair_elim in Hxy. elim Hxy.
  clear Hxy. intro Hxy. exact Hxy. clear Hxy. intro Hxy. exact Hxy.
  intros Exy. unfold singleton. rewrite Exy. apply pair_left.
Qed.

Proposition singleton_injective : forall a b:set,
  singleton a = singleton b -> a = b.
Proof.
  intros a b H. apply singleton_belong. rewrite <- H. apply pair_left.
Qed.

(* useful when dealing with ordered pairs *)
Lemma when_pair_is_singleton : forall a b c:set, 
  {a,b} = singleton c  -> a = b.
Proof.
  intros a b c H. cut (a = c /\ b = c). intros H'. elim H'.
  clear H'. intros Eac Ebc. rewrite Eac, Ebc. reflexivity. split.
  apply singleton_belong. rewrite <- H. apply pair_left.
  apply singleton_belong. rewrite <- H. apply pair_right.
Qed.

(*
Proposition when_subset_singleton : forall a b:set,
  subset a (singleton b) <-> a = O \/ a = singleton b.
Proof.
  intros a b. split.
  intro H. cut (~ a = O \/ a = O). intro H'. elim H'. 
  clear H'. intro H'. right. apply extensionality. exact H.
  unfold subset. intros x Hx. cut (exists y:set, y:a). intro Hy. 
  elim Hy. clear Hy. intros y Hy. apply singleton_belong in Hx.
  rewrite Hx. clear Hx. cut (y = b). intro Eyb. rewrite <- Eyb. exact Hy.
  apply singleton_belong. apply H. exact Hy.

Show.
*)
