Require Import Category.
Require Import Preorder.


Inductive Mor (A:Type) (p:Preorder A) : Type :=
    mor : forall x y:A, rel p x y -> Mor A p. 

Arguments Mor {A} _.
Arguments mor {A} {p} _ _ _.

Parameter eq_bool : forall (A:Type), A -> A -> bool.

Arguments eq_bool {A} _ _.

Axiom eq_bool_correct : forall (A:Type) (x y:A),
    eq_bool x y = true -> x = y.

Axiom eq_bool_correct' : forall (A:Type) (x y:A),
     x = y -> eq_bool x y = true.


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
    eq_bool y y' = true -> rel p x y -> rel p y' z -> rel p x z.
Proof.
    intros Eyy' Hxy Hyz. apply (proof_trans p x y z).
    - exact Hxy.
    - apply eq_bool_correct in Eyy'. rewrite Eyy'. exact Hyz.
Qed.

Arguments trans {A} {p} {x} {y} {y'} {z} _ _ _.

Definition compose_ (A:Type) (p:Preorder A) (f g: Mor p) : option (Mor p) :=
    match f with
    | mor x y pxy   =>
        match g with
        | mor y' z pyz  =>
            match eq_bool y y' as b return eq_bool y y' = b -> option (Mor p) with 
            | true  => fun pr => Some (mor x z (trans pr pxy pyz)) 
            | false => fun _  => None
            end (eq_refl (eq_bool y y'))
        end
    end.

Arguments compose_ {A} {p} _ _.

Definition inner (A:Type) (p:Preorder A) (y y':A) (b:bool) 
    (q:eq_bool y y' = b)(f: eq_bool y y' = true -> Mor p):option (Mor p) :=
        match b as b1 return eq_bool y y' = b1 -> option (Mor p) with
        | true  => fun pr   => Some (f pr)
        | false => fun _    => None
        end q.  

Definition compose2 (A:Type) (p:Preorder A) (f g: Mor p) : option (Mor p) :=
    match f with
    | mor x y pxy   =>
        match g with
        | mor y' z pyz  => 
            inner A p y y' (eq_bool y y') (eq_refl (eq_bool y y'))
                (fun pr => mor x z (trans pr pxy pyz)) 
        end
    end.

Arguments compose2 {A} {p} _ _.

Lemma check_compose : forall (A:Type) (p:Preorder A) (f g:Mor p),
    compose_ f g = compose2 f g.
Proof. intros A p f g. reflexivity. Qed.

Lemma inner_None : forall (A:Type) (p:Preorder A) (y:A) 
    (f:eq_bool y y = true -> Mor p), 
    inner A p y y true (eq_bool_correct' A y y (eq_refl y)) f <> None.
Proof. intros A p y f. unfold inner. intros H. inversion H. Qed.


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
    simpl. split.
    - intros H. inversion H. apply inner_None.

Show.

