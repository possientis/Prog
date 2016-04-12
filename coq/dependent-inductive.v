Set Implicit Arguments.
(* inductive type dependent on a parameter which is not a type, but a value *)

Inductive ltree (n:nat) : Set :=
  | lleaf : ltree n
  | lnode : forall p:nat, p <= n -> ltree n -> ltree n -> ltree n.


Inductive sqrt_data (n:nat) : Set :=
  sqrt_intro : forall x:nat, x*x <= n -> n < (S x)*(S x) -> sqrt_data n.

Lemma certificate_left : 2*2 <= 4.
Proof.
  simpl. apply le_n.
Qed.

Lemma certificate_right : 4 < (S 2)*(S 2).
Proof.
  simpl. unfold lt. apply le_S. apply le_S. apply le_S. apply le_S. apply le_n.
Qed.

Definition two := sqrt_intro certificate_left certificate_right.

Check two. (* sqrt_data 4 *)
