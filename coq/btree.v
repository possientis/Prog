Set Implicit Arguments.
Require Import ZArith.


Inductive Z_btree : Set :=
  | Z_leaf : Z_btree
  | Z_bnode : Z -> Z_btree -> Z_btree -> Z_btree.

Check Z_btree_ind.

Print positive.
(*
Inductive positive : Set :=
xI : positive -> positive | xO : positive -> positive | xH : positive
*)

Print Z.
(*
Inductive Z : Set :=  Z0 : Z | Zpos : positive -> Z | Zneg : positive -> Z
*)

Check positive_ind.
(*
forall P : positive -> Prop,
  (forall p : positive, P p -> P (p~1)%positive) ->
  (forall p : positive, P p -> P (p~0)%positive) ->
   P 1%positive -> forall p : positive, P p
*)

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

Fixpoint Psucc (x:positive) : positive :=
  match x with
    | xI x' => xO (Psucc x') 
    | xO x' => xI x'
    | xH    => 2%positive
  end.

Eval compute in Psucc (234%positive).
Eval compute in Psucc (63%positive).

(*
Open Scope positive_scope.
*)

Eval compute in xO (xO (xO (xI (xO (xI (xI (xI (xI xH)))))))).
Eval compute in (1~1~1~1~1~0~1~0~0~0)%positive. (* 1000 *)
Eval compute in (1~1~0~0~1)%positive.           (* 25 *)
Eval compute in (1~0~0~0~0~0~0~0~0~0)%positive. (* 512 *)

Definition pos_even_bool (n:positive) : bool :=
  match n with
    | xO p      => true
    | xI p      => false
    | xH        => false
  end.

Eval compute in pos_even_bool 1%positive.
Eval compute in pos_even_bool 2%positive.
Eval compute in pos_even_bool 3%positive.









