Require Import Arith.
Require Import Preorder.
Import Nat.

Definition NatPreorder : Preorder nat := preorder
    le
    le_refl
    le_trans
    .

