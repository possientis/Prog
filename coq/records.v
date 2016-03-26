Set Implicit Arguments.
Require Import ZArith.

Inductive plane : Set :=
  | point : Z->Z-> plane.

Check plane_ind. 
(* forall P : plane -> Prop,
   (forall x y : Z, P (point x y)) -> forall p : plane, P p
*)

Definition plane_x (p:plane): Z := 
  match p with point x y => x end.


Definition plane_y (p:plane): Z := 
  match p with point x y => y end.

Reset plane.
Record plane : Set := point { point_x:Z ; point_y:Z }.

Print plane.
Print point_x.

Check plane_rec.



