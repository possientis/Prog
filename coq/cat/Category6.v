Require Import Eq.
Require Import Setoids.



Record Category : Type := category
    { Obj           : Type
    ; Hom           : Obj -> Obj -> Setoid
    ; compose       : forall (a b c:Obj), elems (Hom b c ==> Hom a b ==> Hom a c)
    ; id            : forall (a:Obj), elems (Hom a a)
    ; proof_idl     : forall (a b:Obj) (f:elems (Hom a b)), 
        apply (apply (compose _ _ _) (id b)) f == f
    ; proof_idr     : forall (a b:Obj) (f:elems (Hom a b)),
        apply (apply (compose _ _ _) f) (id a) == f 
    ; proof_assoc   : forall (a b c d:Obj)
        (f:elems (Hom a b))
        (g:elems(Hom b c))
        (h:elems(Hom c d)),
        apply (apply (compose _ _ _) h) (apply (apply (compose _ _ _) g) f)
       == apply (apply (compose _ _ _) (apply (apply (compose _ _ _) h) g)) f
    }
    .

Notation "a :-> b" := (elems (Hom a b))(at level 60, right associativity) : categ.

Arguments Hom {c} _ _.
Arguments compose {c} {a} {b} {c0}.
Arguments id {c} _.
Arguments proof_idl {c} {a} {b} _.
Arguments proof_idr {c} {a} {b} _.
Arguments proof_assoc {c} {a} {b} {c0} {d} _ _ _.


Notation "g @ f" := (apply (apply compose g) f) (at level 60, right associativity). 


(*
Lemma id_left : forall (C:Category) (a b:Obj C) (f:Hom a b), (id b) @ f == f.
Proof. intros C a b f. apply proof_idl. Qed.

Lemma id_right : forall (C:Category) (a b:Obj C) (f:Hom a b), f @ (id a) == f.
Proof. intros C a b f. apply proof_idr. Qed.

Lemma assoc : forall (C:Category)(a b c d:Obj C)(f:Hom a b)(g:Hom b c)(h:Hom c d), 
    h @ (g @ f) == (h @ g) @ f.
Proof. intros C a b c d f g h. apply proof_assoc. Qed.

Lemma compat : forall (C:Category)(a b c:Obj C)(f f':Hom a b)(g g':Hom b c),
    f == f' -> g == g' -> g @ f == g' @ f'.
Proof. intros C a b c f f' g g'. apply proof_compat. Qed.
*)
