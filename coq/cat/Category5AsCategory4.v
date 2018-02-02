Require Import Category4.
Require Import Category5.


(* given a Category5 we define the data necessary to create a Category4 *)

Definition Obj4_ (C:Category5) : Type := Obj C.

Inductive Mor4_ (C:Category5) : Type := 
    mor4_ : forall (a b:Obj C), Hom a b -> Mor4_ C.

Arguments mor4_ {C} _ _ _.

Definition dom4_ (C:Category5) (f:Mor4_ C) : Obj4_ C :=
    match f with
    | mor4_ a _ _       => a
    end.

Definition cod4_ (C:Category5) (f:Mor4_ C) : Obj4_ C :=
    match f with
    | mor4_ _ b _       => b
    end.




