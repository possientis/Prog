Record Category5 : Type := category5
    { Obj5          : Type
    ; Hom5          : Obj5 -> Obj5 -> Type
    ; compose5      : forall (a b c:Obj5), Hom5 a b -> Hom5 b c -> Hom5 a c
    ; id5           : forall (a:Obj5), Hom5 a a
    ; proof_idl5    : forall (a b:Obj5)(f:Hom5 a b), compose5 _ _ _ (id5 a) f = f
    ; proof_idr5    : forall (a b:Obj5)(f:Hom5 a b), compose5 _ _ _ f (id5 b) = f
    ; proof_asc5    : forall (a b c d:Obj5)(f:Hom5 a b)(g:Hom5 b c)(h:Hom5 c d),
        compose5 _ _ _ (compose5 _ _ _ f g) h = 
        compose5 _ _ _ f (compose5 _ _ _ g h)
    }
    .

Definition Obj (C:Category5) : Type := Obj5 C.
Definition Hom (C:Category5)(a b:Obj C) : Type := Hom5 C a b.

Arguments Hom {C} _ _.

Definition compose(C:Category5)(a b c:Obj C)(f:Hom a b)(g:Hom b c) : Hom a c :=
    compose5 C _ _ _ f g.

Arguments compose {C} {a} {b} {c} _ _.

Definition id (C:Category5) (a:Obj C) : Hom a a := id5 C a.

Arguments id {C} _.


Notation "f ; g" := (compose f g) (at level 40, left associativity). 

Theorem id_left : forall (C:Category5) (a b:Obj C) (f: Hom a b), id a ; f = f.
Proof. intros C a b f. apply proof_idl5. Qed.

Theorem id_right : forall (C:Category5) (a b:Obj C) (f: Hom a b), f ; id b = f.
Proof. intros C a b f. apply proof_idr5. Qed.

Theorem compose_assoc : forall (C:Category5) (a b c d:Obj C),
    forall (f:Hom a b) (g:Hom b c) (h: Hom c d), 
        (f ; g) ; h = f ; (g ; h).
Proof. intros C a b c d f g h. apply proof_asc5. Qed.


