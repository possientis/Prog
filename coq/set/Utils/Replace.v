Require Import Peano_dec.

(* replace x by y                                                               *)
Definition replace (x y:nat) (u:nat) : nat :=
    match eq_nat_dec u x with
    | left _    => y    (* if u = x  return y   *)
    | right _   => u    (* otherwise retruen u  *)
    end.
