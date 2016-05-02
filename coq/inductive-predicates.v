(* Set Implicit Arguments.*)

Require Import ZArith.
Require Import List.



Inductive plane : Set :=
  | point : Z->Z-> plane.


Inductive south_west : plane -> plane -> Prop :=
  south_west_def: 
    forall a1 a2 b1 b2:Z, (a1 <= b1)%Z -> (a2 <= b2)%Z ->
      south_west (point a1 a2) (point b1 b2).

Inductive even : nat -> Prop :=
  | O_even        : even 0
  | plus_2_even   : forall n:nat, even n -> even (S (S n)).

(* curly braces '{}' indicate an implicit argument *)
Inductive sorted {A:Set}(R:A->A->Prop) : list A -> Prop :=
  | sorted0       : sorted R nil
  | sorted1       : forall x:A, sorted R (cons x nil)
  | sorted2       : forall (x y:A)(l:list A),
                      R x y -> sorted R (cons y l) -> sorted R (cons x (cons y l)).

Inductive le (n:nat) : nat -> Prop :=
  | le_n          : le n n
  | le_S          : forall m:nat, le n m -> le n (S m).


Definition relation (A:Type) := A -> A -> Prop.

(* transitive closure *)
Inductive clos_trans {A:Type}(R:relation A): A -> A -> Prop :=
  | t_step : forall x y:A, R x y -> clos_trans R x y
  | t_trans: forall x y z:A, clos_trans R x y -> clos_trans R y z
              -> clos_trans R x z.



