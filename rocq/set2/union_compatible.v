Require Import set.
Require Import subset.
Require Import equiv.
Require Import subset_transitive.

Proposition union_compatible: forall (a a' b b':set),
  equiv a a' -> equiv b b' -> equiv (Union a b) (Union a' b').
Proof.
  intros a a' b b' Eaa' Ebb'. 
  elim Eaa'. clear Eaa'. intros Haa' Ha'a.
  elim Ebb'. clear Ebb'. intros Hbb' Hb'b.
  unfold equiv. split.
  apply subset_union_all. split. 
  apply subset_transitive with (b:= a'). exact Haa'. apply subset_x_xUy.
  apply subset_transitive with (b:= b'). exact Hbb'. apply subset_y_xUy. 
  apply subset_union_all. split.
  apply subset_transitive with (b:= a). exact Ha'a. apply subset_x_xUy.
  apply subset_transitive with (b:= b). exact Hb'b. apply subset_y_xUy.
Qed.
  


