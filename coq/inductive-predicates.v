Set Implicit Arguments.
Require Import ZArith.

Inductive plane : Set :=
  | point : Z->Z-> plane.


Inductive south_west : plane -> plane -> Prop :=
  south_west_def: 
    forall a1 a2 b1 b2:Z, (a1 <= b1)%Z -> (a2 <= b2)%Z ->
      south_west (point a1 a2) (point b1 b2).


