Require Import List.

Require Import Eq.
Require Import Coincide.
Require Import Composition.

(* replace x by y                                                               *)
Definition replace (v:Type) (e:Eq v) (x y:v) (u:v) : v :=
    match e u x with
    | left _    => y    (* if u = x  return y   *)
    | right _   => u    (* otherwise return u   *) 
    end.

Arguments replace {v} _ _ _ _.

Open Scope Composition.

(*
Lemma replace_trans : forall (v:Type) (e:Eq v) (x y z:v) (ys:list v),
    ~(In y ys) -> coincide ys (replace e y z ; replace e x y) (replace e x z).
Proof.

Show.
*)

