Require Import Arith.


(* '(Cons x y)' should be thought of '{x}Uy' *)
CoInductive eset : Set :=
  | Empty     : eset
  | Singleton : eset -> eset
  | Union     : eset -> eset -> eset
  | Cons      : eset -> eset -> eset.


(* succ x = {x}Ux *)
Definition succ (x:eset) : eset := Cons x x.

(* from x = {x,x+1,x+2,x+3, ...} *)
CoFixpoint from (x:eset) : eset := Cons x (from (succ x)).

(* N = {0, 1, 2, 3, ... }  *)
Definition N : eset := from Empty.


(*

  (i)   0 <= x
  (ii)  ¬({x} <= 0)
  (iii) {x} <= {y}      <-> (x <= y) /\ (y <= x)
  (iv)  {x} <= yUz      <-> {x} <= y \/ {x} <= z
  (iv)' {x} <= Cons y z <-> {x} <= {y}Uz
  (v)   xUy <= z        <-> x <= z /\ y <= z
  (vi)  Cons x y <= z   <-> {x} <= z /\ y <= z

*)

Fixpoint esubset_n (n:nat) : eset -> eset -> Prop :=
  match n with
    | 0   => (fun _ _     => True)
    | S p => (fun a b     =>
      match a with
        | Empty           => True
        | Singleton x     =>
          match b with
            | Empty       => False
            | Singleton y => esubset_n p x y /\ esubset_n p y x
            | Union y z   => esubset_n p (Singleton x) y \/
                             esubset_n p (Singleton x) z
            | Cons y z    => esubset_n p (Singleton x) (Union (Singleton y) z)
          end
        | Union x y       => esubset_n p x b /\ esubset_n p y b
        | Cons x y        => esubset_n p (Union (Singleton x) y) b
      end)
  end.
