Require Import Category.
Require Import Preorder.


Inductive Mor (A:Type) (p:Preorder A) : Type :=
    mor : forall x y:A, rel p x y -> Mor A p. 


Axiom Axiom_dec : forall (A:Type) (x y:A), {x = y} + { x <> y }.

Arguments Mor {A} _.
Arguments mor {A} {p} _ _ _.

Definition eq_dec (A:Type) (x y: A) : bool.
Proof.
    destruct (Axiom_dec A x y).
    + exact true.
    + exact false. 
Qed.

Arguments eq_dec {A} _ _.

Theorem eq_dec_semantics : forall (A:Type) (x y:A),
    eq_dec x y = true <-> x = y. 
Proof.

Show.

(*
Definition source_ (A:Type) (p:Preorder A) (f : Mor p) : Mor p :=
    match f with
    | mor x _ _     => mor x x (proof_refl p x)
    end.


Definition target_ (A:Type) (p:Preorder A) (f : Mor p) : Mor p :=
    match f with
    | mor _ y _     => mor y y (proof_refl p y)
    end.

Definition compose_ (A:Type) (p:Preorder A) (f g : Mor p) : option (Mor p) :=
*)    



