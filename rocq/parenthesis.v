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
  intros l1 l2 H1 H2. cut (nil++l2 = l2). intro H. rewrite <- H.
  rewrite app_comm_cons with (x:=nil).
  rewrite app_comm_cons with (a:=open). rewrite app_assoc.
  apply wp_concat. apply wp_open_close. exact H1. exact H2. apply app_nil_l.
Qed.


Lemma wp_o_tail_c: forall (l1 l2:list par),
  wp l1 -> wp l2 -> wp (l1 ++ (open :: (l2 ++ (close :: nil)))).
Proof.
  intros l1 l2 H1 H2. apply wp_concat. exact H1. apply wp_open_close. exact H2.
Qed.

Inductive bin : Set :=
  | L : bin
  | N : bin -> bin -> bin.

Fixpoint bin2string (t:bin) : list par :=
  match t with
    | L     => nil
    | N u v => open :: ((bin2string u) ++ (close :: (bin2string v)))
  end.
 
Lemma wp_bin2string: forall t:bin, wp (bin2string t).
Proof.
  intro t. elim t. simpl. apply wp_nil. clear t.
  intros t1 H1 t2 H2. simpl. apply wp_o_head_c. exact H1. exact H2.
Qed.


Fixpoint bin2string' (t:bin) : list par :=
  match t with
    | L     => nil
    | N u v => (bin2string' u) ++ (open :: ((bin2string' v) ++ (close :: nil)))
  end.
 

Lemma wp_bin2string': forall t:bin, wp (bin2string' t).
Proof.
  intro t. elim t. simpl. apply wp_nil. clear t.
  intros t1 H1 t2 H2. simpl. apply wp_o_tail_c. exact H1. exact H2.
Qed.








