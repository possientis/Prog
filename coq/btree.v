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









