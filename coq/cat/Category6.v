Require Import Eq.

Record Category : Type := category
    { Obj           : Type
    ; Hom           : Obj -> Obj -> Type
    ; compose       : forall (a b c:Obj), Hom b c -> Hom a b -> Hom a c
    ; id            : forall (a:Obj), Hom a a
    ; eqHom         : forall (a b:Obj), Eq (Hom a b)
    ; proof_idl     : forall (a b:Obj) (f:Hom a b), 
        eq (eqHom a b) (compose _ _ _ (id b) f) f
    ; proof_idr     : forall (a b:Obj) (f:Hom a b),
        eq (eqHom a b) (compose _ _ _ f (id a)) f 
    ; proof_assoc   : forall (a b c d:Obj)(f:Hom a b)(g:Hom b c)(h:Hom c d),
        eq (eqHom a d)  (compose _ _ _ h (compose _ _ _ g f))
                        (compose _ _ _ (compose _ _ _ h g) f)
    }
    .

Arguments Hom {c} _ _.
Arguments compose {c} {a} {b} {c0} _ _.
Arguments id {c} _.
Arguments eqHom {c} {a} {b}.
Arguments proof_idl {c} {a} {b} _.
Arguments proof_idr {c} {a} {b} _.
Arguments proof_assoc {c} {a} {b} {c0} {d} _ _ _.

Notation "g @ f" := (compose g f) (at level 60, right associativity). 

Notation "f == g" := (eq eqHom f g) (at level 90, no associativity).

Lemma id_left : forall (C:Category) (a b:Obj C) (f:Hom a b), (id b) @ f == f.
Proof. intros C a b f. apply proof_idl. Qed.

Lemma id_right : forall (C:Category) (a b:Obj C) (f:Hom a b), f @ (id a) == f.
Proof. intros C a b f. apply proof_idr. Qed.

Lemma assoc : forall (C:Category)(a b c d:Obj C)(f:Hom a b)(g:Hom b c)(h:Hom c d), 
    h @ (g @ f) == (h @ g) @ f.
Proof. intros C a b c d f g h. apply proof_assoc. Qed.

