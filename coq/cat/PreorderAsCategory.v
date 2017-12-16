Require Import Category.
Require Import Preorder.
Require Import Axiom_ProofIrrelevance.



(* very strong assumption *)

Parameter eq_proof : forall (A:Type) (x y:A), option (x = y).

Arguments eq_proof {A} _ _.

Axiom eq_proof_correct : forall (A:Type) (x y:A), 
    x = y <-> eq_proof x y <> None.

(* end assumption *)



Inductive Mor (A:Type) (p:Preorder A) : Type :=
    mor : forall x y:A, rel p x y -> Mor A p. 

Arguments Mor {A} _.
Arguments mor {A} {p} _ _ _.

Lemma eq_Mor : forall (A:Type) (p:Preorder A) (x x' y y':A), 
    forall (p1: rel p x y) (p2: rel p x' y'), 
    x = x' -> y = y' -> mor x y p1 = mor x' y' p2.
Proof.
    intros A p x x' y y' p1 p2 Exx Eyy. 
    assert (rel p x y = rel p x' y') as H. { apply eq_rel. exact Exx. exact Eyy. } 


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

Arguments source_ {A} {p} _.
Arguments target_ {A} {p} _.

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

Definition trans (A:Type) (p:Preorder A) (x y y' z: A)
    (pyy: y = y') (pxy: rel p x y) (pyz : rel p y' z) : rel p x z.
Proof.
    apply (proof_trans p) with (y:=y).
    - exact pxy.
    - rewrite pyy. exact pyz.
Qed.

Arguments trans {A} {p} {x} {y} {y'} {z} _ _ _.


Definition compose_ (A:Type) (p:Preorder A) (f g: Mor p) : option (Mor p) :=
    match f with
    | mor x y pxy   =>
        match g with
        | mor y' z pyz  =>
            match eq_proof y y' with
            | Some pr   => Some (mor x z (trans pr pxy pyz)) 
            | None      => None     
            end
        end
    end.

Arguments compose_ {A} {p} _ _.

Definition proof_dom_ (A:Type) (p:Preorder A) : forall (f g:Mor p),
    target_ f = source_ g <-> compose_ f g <> None.
Proof.
    intros f g. split.
    - intros H. destruct f as [x y pxy]. destruct g as [y' z pyz].
        simpl in H. inversion H. clear H.
        apply eq_proof_correct in H1. destruct (eq_proof y y') eqn:H'.
        + simpl. rewrite H'. intros H3. inversion H3.
        + exfalso. apply H1. reflexivity.
    - intros H. destruct f as [x y pxy]. destruct g as [y' z pyz].
        simpl. destruct (eq_proof y y') eqn:H'. 
        + assert (y = y').
            { apply eq_proof_correct. rewrite H'. intros H0. inversion H0. }
            rewrite H0. reflexivity.
        + unfold compose_ in H. rewrite H' in H. exfalso. apply H. reflexivity.
Qed.


Definition proof_src_ (A:Type) (p:Preorder A) : forall (f g h: Mor p),
    compose_ f g = Some h -> source_ h = source_ f. 
Proof.
    intros f g h H. 
    destruct f as [x y pxy]. destruct g as [y' z pyz]. destruct h as [x' z' pxz].
    destruct (eq_proof y y') eqn:E.
    - unfold compose_ in H. rewrite E in H. inversion H as [H0].
        simpl. rewrite H0. reflexivity.
    - unfold compose_ in H. rewrite E in H. inversion H.
Qed.
    

Definition proof_tgt_ (A:Type) (p:Preorder A) : forall (f g h: Mor p),
    compose_ f g = Some h -> target_ h = target_ g.
Proof.
    intros f g h H. 
    destruct f as [x y pxy]. destruct g as [y' z pyz]. destruct h as [x' z' pxz].
    destruct (eq_proof y y') eqn:E.
    - unfold compose_ in H. rewrite E in H. inversion H as [H0].  
        simpl. rewrite H1. reflexivity.
    - unfold compose_ in H. rewrite E in H. inversion H.
Qed.

Definition proof_idl (A:Type) (p:Preorder A) : forall (a f:Mor p),
    a = source_ f -> compose_ a f = Some f.
Proof.
    intros a f H. destruct a as [x x' pxx]. destruct f as [x'' y pxy].
    simpl in H. inversion H. destruct (eq_proof x' x'') eqn:E.
    - unfold compose_. rewrite E. 


Show.

*)
