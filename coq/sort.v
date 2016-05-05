Require Import List.

Parameter A:Type.
Parameter R: A -> A -> Prop.
Axiom R_refl:   forall x:A, R x x.
Axiom R_anti:   forall x y:A, R x y -> R y x -> x = y.
Axiom R_trans:  forall x y z:A, R x y -> R y z -> R x z.

Fixpoint sort_n (n:nat): list A -> list A :=
  match n with
    | 0   => (fun _ => nil)
    | S p => (fun l =>
      match l with
        | nil       =>  nil
        | (x::nil)  =>  (x::nil)
        | (x::l')   =>  let m := sort_n n l' in
      end)
  end. 


