Require Import Category.
Require Import Monoid.

(* given a monoid m, we define the data necessary to create a category *)


(* the source of any arrow is the identity of the monoid *)

Definition source_  (A:Type) (m:Monoid A) (x:A) : A := identity m.

Arguments source_ {A} _ _. (* type argument is inferred *)



(* the target of any arrow is the identity of the monoid *) 

Definition target_  (A:Type) (m:Monoid A) (x:A) : A := identity m.

Arguments target_ {A} _ _. (* type argument is inferred *)



(* composition of arrows coincides with the monoid product *)

Definition compose_ (A:Type) (m:Monoid A) (x y: A) : option A := 
    Some (product m x y).

Arguments compose_ {A} _ _ _. (* type argument is inferred *)



(* source of source is source *)

Definition proof_ss_ (A:Type) (m:Monoid A) : forall f:A, 
    source_ m (source_ m f) = source_ m f.
Proof. reflexivity. Qed.


(* target of source is source *)

Definition proof_ts_ (A:Type) (m:Monoid A) : forall f:A,
    target_ m (source_ m f) = source_ m f.
Proof. reflexivity. Qed.



(* target of target is target *)

Definition proof_tt_ (A:Type) (m:Monoid A) : forall f:A,
    target_ m (target_ m f) = target_ m f.
Proof. reflexivity. Qed.



(* source of target is target *)

Definition proof_st_ (A:Type) (m:Monoid A) : forall f:A,
    source_ m (target_ m f) = target_ m f.
Proof. reflexivity. Qed.



(* composition is defined iff target and source line up *) 

Definition proof_dom_ (A:Type) (m:Monoid A) : forall f g:A,
    target_ m f = source_ m g <-> compose_ m f g <> None.
Proof.
    intros f g. split.
    - intros. discriminate. 
    - intros. reflexivity.
Qed.



(* the source of composed arrow is source of first argument *)

Definition proof_src_ (A:Type) (m:Monoid A) : forall f g h: A,
    compose_ m f g = Some h -> source_ m h = source_ m f.
Proof. intros f g h H. clear H. reflexivity. Qed.



(* the target of composed arrow is target of second argument *)

Definition proof_tgt_ (A:Type) (m:Monoid A) : forall f g h: A,
    compose_ m f g = Some h -> target_ m h = target_ m g.
Proof. intros f g h H. clear H. reflexivity. Qed.



(* composing from the left with an object (= identity arrow) has no effect *) 

Definition proof_idl_ (A:Type) (m:Monoid A) : forall a f: A,
    a = source_ m f -> compose_ m a f = Some f.
Proof.
    intros a f H.
    unfold compose_. unfold source_ in H. rewrite H.
    rewrite (proof_idl m). reflexivity.
Qed.



(* composing from the right with an object (= identity arrow) has no effect *)

Definition proof_idr_ (A:Type) (m:Monoid A) : forall a f: A,
    a = target_ m f -> compose_ m f a = Some f.
Proof.
    intros a f H.
    unfold compose_. unfold source_ in H. rewrite H.
    rewrite (proof_idr m). reflexivity.
Qed.



(* composition is associative *)

Definition proof_asc_ (A:Type) (m:Monoid A) : forall f g h fg gh: A,
    compose_ m f g = Some fg ->
    compose_ m g h = Some gh ->
    compose_ m f gh = compose_ m fg h. 
Proof.
    intros f g h fg gh H H'. unfold compose_ in H. unfold compose_ in H'.
    injection H. clear H. intro H.
    injection H'. clear H'. intro H'.
    rewrite <- H. rewrite <- H'. unfold compose_. 
    rewrite (proof_asc m). reflexivity.
Qed.


(* A monoid with support A, can be turned into a category with support A *)

Definition toCategory (A:Type) (m:Monoid A) : Category A := category
    (source_      m)
    (target_      m)
    (compose_     m)
    (proof_ss_  A m)
    (proof_ts_  A m)
    (proof_tt_  A m)
    (proof_st_  A m)
    (proof_dom_ A m)
    (proof_src_ A m)
    (proof_tgt_ A m)
    (proof_idl_ A m)
    (proof_idr_ A m)
    (proof_asc_ A m).

Arguments toCategory {A} _.


