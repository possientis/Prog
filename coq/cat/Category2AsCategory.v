Require Import Category2.
Require Import Category.

(* given a category2, we define the data necessary to create a category *)

Definition source_ (Obj Mor:Type) (c:Category2 Obj Mor) (f:Mor) : Mor := 
    id c (dom c f). 

Definition target_ (Obj Mor:Type) (c:Category2 Obj Mor) (f:Mor) : Mor := 
    id c (cod c f). 
