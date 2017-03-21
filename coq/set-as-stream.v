Set Implicit Arguments.

CoInductive set : Set :=
  | nil   : set
  | cons  : set -> set -> set. (* conx x y = {x}Uy *)

Inductive belong (x: set) (y: set) : Prop :=
  | car   : forall xs:set, y = (cons x xs) -> belong x y
  | cdr   : forall a ys:set, belong x ys -> y = cons a ys -> belong x y.

Definition subset (x y:set) : Prop := forall z:set, belong z x -> belong z y.

Definition equiv (x y:set) : Prop := subset x y /\ subset y x.

Lemma subset_refl: forall x:set, subset x x.
Proof.
  intro x. unfold subset. intros z H. exact H.
Qed.

Lemma subset_trans: forall x y z: set,
  subset x y -> subset y z -> subset x z.
Proof.
  intros x y z Hxy Hyz. unfold subset. intros t H. apply Hyz. apply Hxy. exact H.
Qed.

Lemma subset_anti: forall x y:set,
  subset x y -> subset y x -> equiv x y.
Proof.
  intros x y Hxy Hyx. unfold equiv. split. exact Hxy. exact Hyx.
Qed.



(*
Definition empty_set : set := nil.

Definition singleton (x:set) : set := cons x nil.  

Definition pair (x y:set) : set := cons x (cons y nil).
*)



