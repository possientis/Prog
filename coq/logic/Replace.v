Require Import Eq.

(* replace x by y                                                               *)
Definition replace (v:Type) (p:Eq v) (x y:v) (u:v) : v :=
    match p u x with
    | left _    => y    (* if u = x  return y   *)
    | right _   => u    (* otherwise return u   *) 
    end.

Arguments replace {v} _ _ _ _.

