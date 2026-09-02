Require Import Arith.

Record RatPlus : Set :=
  mkRat { top:nat ; bottom:nat ; bottom_condition: bottom <> 0 }.

(* this axiom leads to inconsistent theory, see below *)
Axiom eq_RatPlus : forall r s: RatPlus, 
  top r * bottom s = top s * bottom r -> r = s.

Lemma L1: 1 <> 0.
Proof.
unfold not. intro H. discriminate H.
Qed.

Lemma L2: 2 <> 0.
Proof.
  unfold not. intro H. discriminate H.
Qed.

Definition r := mkRat 1 1 L1.
Definition s := mkRat 2 2 L2.

Lemma L3: r = s.
Proof.
  apply eq_RatPlus. simpl. reflexivity.
Qed.

Lemma L4: r <> s.
Proof.
  unfold not. intro H. discriminate H.
Qed.


Theorem inconsistent: False.
Proof. 
  apply L4. apply L3.
Qed.
