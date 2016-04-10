Inductive cmp : Set :=
  | Less :    cmp
  | Equal:    cmp
  | Greater : cmp.

Fixpoint three_way_compare (n m: nat) : cmp :=
  match n,m with
    | 0, 0        => Equal
    | 0, S q      => Less
    | S p, 0      => Greater
    | S p, S q    => three_way_compare p q
  end.

Eval compute in three_way_compare 34 67.
Eval compute in three_way_compare 67 67.
Eval compute in three_way_compare 90 67.
