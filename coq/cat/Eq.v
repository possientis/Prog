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

Definition prod_eq (a b:Type) (eqa:Eq a) (eqb:Eq b) (x y: a * b) : Prop :=
    match x, y with
    | (xa,xb), (ya,yb) => equal eqa xa ya /\ equal eqb xb yb
    end.

Arguments prod_eq {a} {b} _ _ _ _.

Lemma prod_refl : forall (a b:Type) (eqa:Eq a) (eqb:Eq b) (x:a * b),
    prod_eq eqa eqb x x.
Proof.
    intros a b eqa eqb [xa xb]. split.
    - apply refl.
    - apply refl.
Qed.

Arguments prod_refl {a} {b} _ _ _.

Lemma prod_sym : forall (a b:Type) (eqa:Eq a) (eqb:Eq b) (x y:a * b),
    prod_eq eqa eqb x y -> prod_eq eqa eqb y x.
Proof.
    intros a b eqa eqb [xa xb] [ya yb] [Ha Hb]. split.
    - apply sym. exact Ha.
    - apply sym. exact Hb.
Qed.

Arguments prod_sym {a} {b} _ _ _ _ _.

Lemma prod_trans : forall (a b:Type) (eqa:Eq a) (eqb:Eq b) (x y z:a * b),
    prod_eq eqa eqb x y -> prod_eq eqa eqb y z -> prod_eq eqa eqb x z.
Proof.
    intros a b eqa eqb [xa xb] [ya yb] [za zb] [Ha Hb] [Ha' Hb']. split.
    - apply trans with (y:=ya).
        + exact Ha.
        + exact Ha'.
    - apply trans with (y:=yb).
        + exact Hb.
        + exact Hb'.
Qed.

Arguments prod_trans {a} {b} _ _ _ _ _ _ _.

Definition prodEq (a b:Type) (eqa:Eq a) (eqb:Eq b) : Eq (a * b) := equality
    (prod_eq    eqa eqb)
    (prod_refl  eqa eqb)
    (prod_sym   eqa eqb)
    (prod_trans eqa eqb).

Arguments prodEq {a} {b} _ _.


