Set Implicit Arguments.

Require Import set.
Require Import subset.
Require Import equiv.

Lemma equiv_symmetric : forall (a b:set),
  equiv a b <-> equiv b a.
Proof.
  intros a b. unfold equiv. simpl. split. 
  intro H. split. 
  apply proj2 with (A:= subset a b). exact H.
  apply proj1 with (B:= subset b a). exact H.
  intro H. split.
  apply proj2 with (A:= subset b a). exact H.
  apply proj1 with (B:= subset a b). exact H.
Qed.


