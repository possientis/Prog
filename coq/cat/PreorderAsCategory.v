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

Arguments source_ {A} {p} _.
Arguments target_ {A} {p} _.

Lemma trans (A:Type) (p:Preorder A) (x y y' z:A) :
    eq_dec y y' = true -> rel p x y -> rel p y' z -> rel p x z.
Proof.
    intros Eyy' Hxy Hyz. apply (proof_trans p x y z).
    - exact Hxy.
    - apply eq_dec_correct in Eyy'. rewrite Eyy'. exact Hyz.
Qed.

Arguments trans {A} {p} {x} {y} {y'} {z} _ _ _.

(* example of application of the convoy pattern key idea: having access 
   within the code of a proof of the equality over which you pattern match *)

Definition test (A:Type) (x y:A) : option (x = y) :=
    match eq_dec x y as b return eq_dec x y = b -> option (x = y) with
    | true  => fun p => Some (eq_dec_correct A x y p)
    | false => fun _ => None
    end (eq_refl (eq_dec x y)).

Definition compose_ (A:Type) (p:Preorder A) (f g : Mor p) : option (Mor p) :=
    match f with
    | mor x y pxy   =>
        match g with
        | mor y' z pyz  =>
            match eq_dec y y' as b return eq_dec y y' = b -> option (Mor p) with 
            | true  => fun pr => Some (mor x z (trans pr pxy pyz)) 
            | False => fun _  => None
            end (eq_refl (eq_dec y y'))
        end
    end.

Arguments compose_ {A} {p} _ _.

Definition proof_ss_ (A:Type) (p:Preorder A) : forall (f:Mor p),
   source_ (source_ f) = source_ f. 
Proof. intros f. destruct f as [x y pxy]. reflexivity. Qed.


Definition proof_ts_ (A:Type) (p:Preorder A) : forall (f:Mor p),
   target_ (source_ f) = source_ f. 
Proof. intros f. destruct f as [x y pxy]. reflexivity. Qed.


Definition proof_tt_ (A:Type) (p:Preorder A) : forall (f:Mor p),
   target_ (target_ f) = target_ f. 
Proof. intros f. destruct f as [x y pxy]. reflexivity. Qed.

Definition proof_st_ (A:Type) (p:Preorder A) : forall (f:Mor p),
   source_ (target_ f) = target_ f. 
Proof. intros f. destruct f as [x y pxy]. reflexivity. Qed.

Definition proof_dom_ (A:Type) (p:Preorder A) : forall (f g:Mor p),
    target_ f = source_ g <-> compose_ f g <> None.
Proof.
    intros f g. destruct f as [x y pxy]. destruct g as [y' z pyz].
    simpl. 


Show.




