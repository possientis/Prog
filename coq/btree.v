Set Implicit Arguments.
Require Import ZArith.


Inductive Z_btree : Set :=
  | Z_leaf : Z_btree
  | Z_bnode : Z -> Z_btree -> Z_btree -> Z_btree.

Check Z_btree_ind.

(*
Open Scope Z_scope.
*)

Fixpoint sum_all_values (t: Z_btree) : Z :=
  (match t with
    | Z_leaf          => 0
    | Z_bnode v t1 t2 => v + sum_all_values t1 + sum_all_values t2
  end)%Z.  (* (...)%Z or else you need to open Z_scope *)

Fixpoint zero_present (t: Z_btree) : bool :=
  match t with
    | Z_leaf              => false
    | Z_bnode (0%Z) t1 t2 => true
    | Z_bnode _ t1 t2     => if zero_present t1 then true else zero_present t2
  end.

Inductive Z_fbtree : Set :=
  | Z_fleaf : Z_fbtree
  | Z_fnode : Z -> (bool->Z_fbtree) -> Z_fbtree.


Definition right_son (t: Z_btree) : Z_btree :=
  match t with
    | Z_leaf            => Z_leaf
    | Z_bnode a t1 t2   => t2
  end.

Definition fright_son (t: Z_fbtree) : Z_fbtree :=
  match t with 
    | Z_fleaf           => Z_fleaf
    | Z_fnode a f       => f false
  end.

Fixpoint fsum_all_values (t:Z_fbtree) : Z :=
  (match t with 
    | Z_fleaf           => 0
    | Z_fnode v f       => v + fsum_all_values (f true) + fsum_all_values (f false)
  end)%Z.


Fixpoint fzero_present (t:Z_fbtree) : bool :=
  match t with
    | Z_fleaf           => false
    | Z_fnode (0%Z) f   => true
    | Z_fnode _     f   => if fzero_present (f true) then true else fzero_present (f false) 
  end.


Inductive Z_inf_branch_tree : Set :=
  | Z_inf_leaf : Z_inf_branch_tree
  | Z_inf_node : Z -> (nat -> Z_inf_branch_tree) -> Z_inf_branch_tree. 


Fixpoint sum_f_acc (n:nat)(f: nat->Z)(acc: Z) :Z :=
  match n with
    | 0     => acc
    | S p   => sum_f_acc p f (acc + (f p))
  end.

Definition sum_f (n:nat)(f:nat->Z) : Z  := sum_f_acc n f 0%Z.

Fixpoint n_sum_all_values (n:nat)(t: Z_inf_branch_tree) : Z :=
  (match t with 
    | Z_inf_leaf          => 0
    | Z_inf_node v f      => v + sum_f n (fun x:nat => n_sum_all_values n (f x))
  end)%Z.

Theorem plus_assoc' : forall x y z:nat, x+y+z = x+(y+z).
Proof.
  intros x y z. elim x. simpl. trivial.
  intros n H. simpl. rewrite H. trivial.
Qed.


