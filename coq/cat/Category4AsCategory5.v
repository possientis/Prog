Require Import Category4.
Require Import Category5.

(* given a Category4 we define the data necessary to create a Category5 *)

Definition Obj5_ (C:Category4) : Type := Obj4 C.

Inductive Hom5_ (C:Category4) (a b:Obj5_ C) : Type :=
| hom5_ : forall (f:Mor4 C), dom4 C f = a -> cod4 C f = b -> Hom5_ C a b
.

(*
Definition compose5_(C:Category4)(a b c: Obj5_ C)(f:Hom5_ C a b)(g:Hom5_ C b c)
    : Hom5_ C a c :=
        hom5_  
*)
