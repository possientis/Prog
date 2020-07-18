Require Import Peano_dec.

(* replace x by y, all else is unchanged                                        *)
Definition replace (x y:nat) (u:nat) : nat :=
    match eq_nat_dec u x with
    | left _    => y        (* if u = x  return y   *)
    | right _   => u        (* otherwise return u   *)
    end.

(* replace x by y and x' by y', all else is unchanged                           *)
Definition replace2 (x x' y y':nat) (u:nat) : nat :=
    match eq_nat_dec u x with
    | left _    => y        (* if u = x  return y   *)
    | right _   =>
        match eq_nat_dec u x' with
        | left _    => y'   (* if u = x' return y'  *)
        | right _   => u    (* otherwise return u   *)
        end
    end.
