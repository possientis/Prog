Require Import Arith.
Require Import Preorder.

Definition NatPreorder : Preorder nat := preorder
    le
    le_refl
    le_trans
    .

