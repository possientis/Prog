Require Import Peano_dec.

(* replace x by x', all else is unchanged                                        *)
Definition replace (x x':nat) (u:nat) : nat :=
    match eq_nat_dec u x with
    | left _    => x'       (* if u = x  return x'  *)
    | right _   => u        (* otherwise return u   *)
    end.

(* replace x by x' and y by y', all else is unchanged                           *)
Definition replace2 (x y x' y':nat) (u:nat) : nat :=
    match eq_nat_dec u x with
    | left _    => x'       (* if u = x  return x'  *)
    | right _   =>
        match eq_nat_dec u y with
        | left _    => y'   (* if u = y  return y'  *)
        | right _   => u    (* otherwise return u   *)
        end
    end.
