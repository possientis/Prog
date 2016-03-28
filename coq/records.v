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
Check Zabs_nat.

Definition manhattan_dist (p q: plane) : nat :=
  Zabs_nat(point_x p - point_x q) +
  Zabs_nat(point_y p - point_y q).


Inductive vehicle : Set :=
  | bicycle : nat -> vehicle
  | motorized : nat -> nat -> vehicle.

Check vehicle_ind.
(*
forall P : vehicle -> Prop,
  (forall n : nat, P (bicycle n)) ->
  (forall n n0 : nat, P (motorized n n0)) -> forall v : vehicle, P v
*)

Definition nb_wheels (v:vehicle) : nat :=
  match v with
  | bicycle x     => 2
  | motorized x n => n
  end.

Definition nb_seats (v:vehicle) : nat :=
  match v with
  | bicycle x     => x
  | motorized x _ => x
  end.

Check vehicle_rec.
(*
 forall P : vehicle -> Set,
 (forall n : nat, P (bicycle n)) ->
 (forall n n0 : nat, P (motorized n n0)) -> forall v : vehicle, P v
*)

Definition nb_seats' := vehicle_rec (fun v => nat) (fun n => n) (fun n m => n).

Lemma Lemma_seats: forall v:vehicle, nb_seats v = nb_seats' v.
Proof.
  intro v. pattern v. apply vehicle_ind. intro n. reflexivity. intros n m. reflexivity.
Qed.

Theorem bicycle_not_motorized: forall n m p: nat, bicycle n <> motorized m p. 
Proof.
  intros n m p. unfold not. intro H. (* discriminate H. *)
  pose (g:=fun (v:vehicle) => match v with bicycle x => True | motorized x y => False end).
  change (g (motorized m p)). rewrite <- H. simpl. apply I.
Qed.

Theorem bicycle_eq_seats: forall x y: nat, bicycle x = bicycle y -> x = y.
Proof.
  intros x y H. change (x = nb_seats (bicycle y)). rewrite <- H. simpl. apply eq_refl.
Qed.

Theorem bicycle_eq_seats': forall x y: nat, bicycle x = bicycle y -> x = y.
Proof.
  intros x y H. injection H. trivial. 
Qed.





