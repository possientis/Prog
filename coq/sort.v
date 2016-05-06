Require Import List.

Parameter A:Type.
Parameter R: A -> A -> Prop.
Axiom R_refl:   forall x:A, R x x.
Axiom R_anti:   forall x y:A, R x y -> R y x -> x = y.
Axiom R_trans:  forall x y z:A, R x y -> R y z -> R x z.
Axiom R_total:  forall x y:A, R x y \/ ~R x y.


Fixpoint sort_n (n:nat): list A -> list A :=
  match n with
    | 0   => (fun _ => nil)
    | S p => (fun l =>
      match l with
        | nil       =>  nil
        | (x::nil)  =>  (x::nil)
        | (x::l')   =>  let m := sort_n p l' in
                        let y := hd_error m  in
                        match y with
                          | None    => nil (* should not happen *)
                          | Some z  => nil 
                        end
      end)
  end. 

