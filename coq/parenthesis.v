Require Import List.


Inductive par : Set := open | close.

Inductive wp : list par -> Prop :=
  | wp_nil          : wp nil
  | wp_open_close   : forall (l:list par), wp l -> wp ((open::l)++(close::nil))
  | wp_concat       : forall (l1 l2: list par), wp l1 -> wp l2 -> wp (l1++l2). 


Lemma wp_oc: wp (open::close::nil).
Proof.
  apply wp_open_close with (l:=nil). apply wp_nil.
Qed.

Lemma wp_o_head_c: forall (l1 l2:list par),
  wp l1 -> wp l2 -> wp (open::(l1++(close::l2))).
Proof.
  intros l1 l2. 
