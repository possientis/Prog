Require Import category.
Require Import monoid.

(* given a monoid m, we define the data necessary to create a category *)

Definition source_  {A:Type} (m:Monoid A) (x:A) : A := identity m.

Definition target_  {A:Type} (m:Monoid A) (x:A) : A := identity m.

Definition compose_ {A:Type} (m:Monoid A) (x y: A) : option A := 
    Some (product m x y).

Definition proof_ss_ {A:Type} (m:Monoid A) : forall f:A, 
    source_ m (source_ m f) = source_ m f.
Proof. reflexivity. Qed.

Definition proof_ts_ {A:Type} (m:Monoid A) : forall f:A,
    target_ m (source_ m f) = source_ m f.
Proof. reflexivity. Qed.

Definition proof_tt_ {A:Type} (m:Monoid A) : forall f:A,
    target_ m (target_ m f) = target_ m f.
Proof. reflexivity. Qed.

Definition proof_st_ {A:Type} (m:Monoid A) : forall f:A,
    source_ m (target_ m f) = target_ m f.
Proof. reflexivity. Qed.

Definition proof_dom_ {A:Type} (m:Monoid A) : forall f g:A,
    target_ m f = source_ m g <-> compose_ m f g <> None.
Proof.
    intros f g. split.
    - intros. discriminate. 
    - intros. reflexivity.
Qed.

Definition proof_src_ {A:Type} (m:Monoid A) : forall f g h: A,
    compose_ m f g = Some h -> source_ m h = source_ m f.
Proof. intros f g h H. clear H. reflexivity. Qed.

Definition proof_tgt_ {A:Type} (m:Monoid A) : forall f g h: A,
    compose_ m f g = Some h -> target_ m h = target_ m g.
Proof. intros f g h H. clear H. reflexivity. Qed.

Definition proof_idl_ {A:Type} (m:Monoid A) : forall a f: A,
    a = source_ m f -> compose_ m a f = Some f.
Proof.
    intros a f H.
    unfold compose_. unfold source_ in H. rewrite H.
    rewrite (proof_idl m). reflexivity.
Qed.

Definition proof_idr_ {A:Type} (m:Monoid A) : forall a f: A,
    a = source_ m f -> compose_ m f a = Some f.
Proof.
    intros a f H.
    unfold compose_. unfold source_ in H. rewrite H.
    rewrite (proof_idr m). reflexivity.
Qed.

Definition proof_asc_ {A:Type} (m:Monoid A) : forall f g h fg gh: A,
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
    (source_    m)
    (target_    m)
    (compose_   m)
    (proof_ss_  m)
    (proof_ts_  m)
    (proof_tt_  m)
    (proof_st_  m)
    (proof_dom_ m)
    (proof_src_ m)
    (proof_tgt_ m)
    (proof_idl_ m)
    (proof_idr_ m)
    (proof_asc_ m).

Arguments toCategory {A}.

(* turning the monoid Nat into a category *)
Definition NatAsCat : Category nat := toCategory Nat.

(*
Check NatAsCat.
*)

(* the source of every morphism is the identity of the monoid *)
Example source_test : forall n:nat, source NatAsCat n = 0.
Proof. reflexivity. Qed.

(* the target of every morphism is the identity of the monoid *)
Example target_test : forall n:nat, target NatAsCat n = 0.
Proof. reflexivity. Qed.

(* composition is defined everywhere and coincides with summation *)
Example compose_test : forall n m:nat, compose NatAsCat n m = Some (n + m).
Proof. reflexivity. Qed.




