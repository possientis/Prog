Record Eq (a:Type) : Type := equality 
    { equal : a -> a -> Prop
    ; refl  : forall (x:a), equal x x
    ; sym   : forall (x y:a), equal x y -> equal y x
    ; trans : forall (x y z:a), equal x y -> equal y z -> equal x z
    }
    . 

Arguments equal {a} _ _ _.
Arguments equality {a} _ _ _ _.

(* default equality for any type *)
Definition defEq (a:Type) : Eq a := equality
    (@eq a)
    (@eq_refl a)
    (@eq_sym a)
    (@eq_trans a).

Arguments defEq {a}.



