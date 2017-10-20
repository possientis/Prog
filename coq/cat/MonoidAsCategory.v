Require Import category.
Require Import monoid.

(* given a monoid m, we define the data necessary to create a category *)

Definition msource  {A:Type} (m:Monoid A) (x:A) : A := identity m.

Definition mtarget  {A:Type} (m:Monoid A) (x:A) : A := identity m.

Definition mcompose {A:Type} (m:Monoid A) (x y: A) : option A := 
    Some (product m x y).

Definition proof_ss_ {A:Type} (m:Monoid A) : forall f:A, 
    msource m (msource m f) = msource m f.
Proof. reflexivity. Qed.

Definition proof_ts_ {A:Type} (m:Monoid A) : forall f:A,
    mtarget m (msource m f) = msource m f.
Proof. reflexivity. Qed.

Definition proof_tt_ {A:Type} (m:Monoid A) : forall f:A,
    mtarget m (mtarget m f) = mtarget m f.
Proof. reflexivity. Qed.

Definition proof_st_ {A:Type} (m:Monoid A) : forall f:A,
    msource m (mtarget m f) = mtarget m f.
Proof. reflexivity. Qed.

Definition proof_dom_ {A:Type} (m:Monoid A) : forall f g:A,
    mtarget m f = msource m g <-> mcompose m f g <> None.
Proof.
    intros f g. split.
    - intros. discriminate. 
    - intros. reflexivity.
Qed.

Definition proof_src_ {A:Type} (m:Monoid A) : forall f g h: A,
    mcompose m f g = Some h -> msource m h = msource m f.
Proof. intros f g h H. clear H. reflexivity. Qed.

Definition proof_tgt_ {A:Type} (m:Monoid A) : forall f g h: A,
    mcompose m f g = Some h -> mtarget m h = mtarget m g.
Proof. intros f g h H. clear H. reflexivity. Qed.

Definition proof_idl_ {A:Type} (m:Monoid A) : forall a f: A,
    a = msource m a -> 
    a = mtarget m a -> 
    a = msource m f -> mcompose m a f = Some f.
Proof.
    intros a f H H1 H2. clear H1 H2. 
    unfold mcompose. unfold msource in H. rewrite H.
    rewrite (proof_idl A m). reflexivity.
Qed.

Definition proof_idr_ {A:Type} (m:Monoid A) : forall a f: A,
    a = msource m a -> 
    a = mtarget m a -> 
    a = msource m f -> mcompose m f a = Some f.
Proof.
    intros a f H H1 H2. clear H1 H2. 
    unfold mcompose. unfold msource in H. rewrite H.
    rewrite (proof_idr A m). reflexivity.
Qed.

Definition proof_asc_ {A:Type} (m:Monoid A) : forall f g h fg gh: A,
    mcompose m f g = Some fg ->
    mcompose m g h = Some gh ->
    mcompose m f gh = mcompose m fg h. 
Proof.
    intros f g h fg gh H H'. unfold mcompose in H. unfold mcompose in H'.
    injection H. clear H. intro H.
    injection H'. clear H'. intro H'.
    rewrite <- H. rewrite <- H'. unfold mcompose. 
    rewrite (proof_asc A m). reflexivity.
Qed.

(* A monoid with support A, can be turned into a category with support A *)
Definition toCategory {A:Type} (m:Monoid A) : Category A := category A
    (msource m)
    (mtarget m)
    (mcompose m)
    (proof_ss_ m)
    (proof_ts_ m)
    (proof_tt_ m)
    (proof_st_ m)
    (proof_dom_ m)
    (proof_src_ m)
    (proof_tgt_ m)
    (proof_idl_ m)
    (proof_idr_ m)
    (proof_asc_ m).

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




