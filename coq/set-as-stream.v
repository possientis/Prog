Set Implicit Arguments.

CoInductive set : Set :=
  | nil   : set
  | cons  : set -> set -> set. (* conx x y = {x}Uy *)

Inductive belong (x: set) (y: set) : Prop :=
  | car   : forall xs:set, y = (cons x xs) -> belong x y
  | cdr   : forall a ys:set, belong x ys -> y = cons a ys -> belong x y.

Definition subset (x y:set) : Prop := forall z:set, belong z x -> belong z y.

Definition equiv (x y:set) : Prop := subset x y /\ subset y x.

(*****************************************************************************)
(*                      subset is a partial order                            *)
(*****************************************************************************)

Proposition subset_refl: forall x:set, subset x x.
Proof.
  intro x. unfold subset. intros z H. exact H.
Qed.

Proposition subset_trans: forall x y z: set,
  subset x y -> subset y z -> subset x z.
Proof.
  intros x y z Hxy Hyz. unfold subset. intros t H. apply Hyz. apply Hxy. exact H.
Qed.

Proposition subset_anti: forall x y:set,
  subset x y -> subset y x -> equiv x y.
Proof.
  intros x y Hxy Hyx. unfold equiv. split. exact Hxy. exact Hyx.
Qed.


(*****************************************************************************)
(*                      equiv is an equivalence                              *)
(*****************************************************************************)

Proposition equiv_refl: forall x:set, equiv x x.
Proof.
  intro x. unfold equiv. split. apply subset_refl. apply subset_refl.
Qed.

Proposition equiv_sym: forall x y:set, equiv x y -> equiv y x.
Proof.
  intros x y H. unfold equiv. split. 
  unfold equiv in H. elim H. clear H. intros Hxy Hyx. exact Hyx.
  unfold equiv in H. elim H. clear H. intros Hxy Hyx. exact Hxy.
Qed.

Proposition equiv_trans: forall x y z:set,
  equiv x y -> equiv y z -> equiv x z.
Proof.
  intros x y z Hxy Hyz. unfold equiv. split.
  apply subset_trans with (y:=y). apply Hxy. apply Hyz.
  apply subset_trans with (y:=y). apply Hyz. apply Hxy.
Qed.


(*****************************************************************************)
(*                     Compatibility of relation                             *)
(*****************************************************************************)

Definition compatible (relation : set -> set -> Prop) : Prop := 
  forall x y x' y': set, equiv x x' -> equiv y y'->
    relation x y -> relation y x.

  


(*
Definition empty_set : set := nil.

Definition singleton (x:set) : set := cons x nil.  

Definition pair (x y:set) : set := cons x (cons y nil).
*)



