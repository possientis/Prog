Require Import Category.
Require Import Preorder.


Inductive Mor (A:Type) (p:Preorder A) : Type :=
    mor : forall x y:A, rel p x y -> Mor A p. 

Arguments Mor {A} _.
Arguments mor {A} {p} _ _ _.

Parameter eq_dec : forall (A:Type), A -> A -> bool.

Arguments eq_dec {A} _ _.

Axiom eq_dec_correct : forall (A:Type) (x y:A),
    eq_dec x y = true -> x = y.


Definition source_ (A:Type) (p:Preorder A) (f : Mor p) : Mor p :=
    match f with
    | mor x _ _     => mor x x (proof_refl p x)
    end.


Definition target_ (A:Type) (p:Preorder A) (f : Mor p) : Mor p :=
    match f with
    | mor _ y _     => mor y y (proof_refl p y)
    end.


Definition compose_ (A:Type) (p:Preorder A) (f g : Mor p) : option (Mor p) :=
    match f with
    | mor x y pxy   =>
        match g with
        | mor y' z pyz  =>
            match eq_dec y y' with 
            | true  => Some (mor x y pxy)
            | False => None
            end
        end
    end.

Definition test (A:Type) (x y:A) : option (x = y) :=
    match eq_dec x y with
    | true  => Some (eq_dec_correct A x y _)
    | false => None
    end.







