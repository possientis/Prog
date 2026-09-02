Require Import Class.

Definition unitEqual (x y:unit) : Prop := True.

Lemma unitRefl : forall (x:unit), unitEqual x x.
Proof.
    intros x. unfold unitEqual. trivial.
Qed.

Lemma unitSymm : forall (x y:unit), unitEqual x y -> unitEqual y x.
Proof.
    intros x y H. unfold unitEqual. trivial.
Qed.

Lemma unitTran : forall (x y z:unit), 
    unitEqual x y -> unitEqual y z -> unitEqual x z.
Proof.
    intros x y z H1 H2. unfold unitEqual. trivial.
Qed.

Instance unitEq : Eq unit :=
    { equal := unitEqual
    ; refl  := unitRefl
    ; sym   := unitSymm
    ; trans := unitTran
    }. 


