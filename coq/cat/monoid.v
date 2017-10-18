Require Import Arith.

Record Monoid (A:Type) : Type := monoid 
    {   identity    : A
    ;   product     : A -> A -> A
    ;   proof_idl   : forall x:A, product identity x = x
    ;   proof_idr   : forall x:A, product x identity = x
    ;   proof_asc   : forall x y z:A, 
            product x (product y z) = 
            product (product x y) z 
    }
    .

Definition Nat : Monoid nat := monoid nat
    0 
    plus plus_0_l 
    plus_0_r 
    plus_assoc
    .

Example identity_test : identity nat Nat = 0.
Proof. reflexivity. Qed. 

Example product_test : product nat Nat 3 4 = 7. 
Proof. reflexivity. Qed. 

(* given a monoid m, we define the data necessary to create a category *)

Definition source_  {A:Type} (m:Monoid A) (x: option A) : option A := None.

Definition target_  {A:Type} (m:Monoid A) (x: option A) : option A := None.

Definition product_ {A:Type} (m:Monoid A) (x y: option A) : option (option A) :=
    match x with
        | None    => Some y
        | Some x' => 
            match y with
                | None      => Some x
                | Some y'   => Some (Some (product A m x' y'))
            end
    end.

Definition proof_ss_ {A:Type} (m:Monoid A) : forall f:option A, 
    source_ m (source_ m f) = source_ m f.
Proof. reflexivity. Qed.

Definition proof_ts_ {A:Type} (m:Monoid A) : forall f:option A,
    target_ m (source_ m f) = source_ m f.
Proof. reflexivity. Qed.

Definition proof_tt_ {A:Type} (m:Monoid A) : forall f:option A,
    target_ m (target_ m f) = target_ m f.
Proof. reflexivity. Qed.

Definition proof_st_ {A:Type} (m:Monoid A) : forall f:option A,
    source_ m (target_ m f) = target_ m f.
Proof. reflexivity. Qed.

Definition proof_dom_ {A:Type} (m:Monoid A) : forall f g:option A,
    target_ m f = source_ m g <-> product_ m f g <> None.
Proof.
    intros f g. split.
    - intros H. clear H. destruct f, g.
        + discriminate.
        + discriminate.
        + discriminate.
        + discriminate.
    - intros H. clear H. reflexivity.
Qed.

Definition proof_src_ {A:Type} (m:Monoid A) : forall f g h: option A,
    product_ m f g = Some h -> source_ m h = source_ m f.
Proof. intros f g h H. clear H. reflexivity. Qed.

Definition proof_tgt_ {A:Type} (m:Monoid A) : forall f g h: option A,
    product_ m f g = Some h -> target_ m h = target_ m g.
Proof. intros f g h H. clear H. reflexivity. Qed.

Definition proof_idl_ {A:Type} (m:Monoid A) : forall a f: option A,
    a = source_ m a -> 
    a = target_ m a -> 
    a = source_ m f -> product_ m a f = Some f.
Proof.
    intros a f H H1 H2. clear H1 H2. 
    unfold source_ in H. rewrite H. reflexivity.
Qed.

Definition proof_idr_ {A:Type} (m:Monoid A) : forall a f: option A,
    a = source_ m a -> 
    a = target_ m a -> 
    a = source_ m f -> product_ m f a = Some f.
Proof.
    intros a f H H1 H2. clear H1 H2. 
    unfold source_ in H. rewrite H. clear H.
    destruct f.
    - reflexivity.
    - reflexivity.
Qed.

Definition proof_asc_ {A:Type} (m:Monoid A) : forall f g h fg gh: option A,
    product_ m f g = Some fg ->
    product_ m g h = Some gh ->
    product_ m fg h = product_ m f gh.
Proof.
    intros f g h fg gh. destruct f,g,h,fg,gh.
    - intros H1 H2. simpl in H1. simpl in H2. simpl.

Show.


(*
Check Nat.
Check support Nat.
Check identity Nat.
Check product Nat.
Check proof_idl Nat.
Check proof_idr Nat.
Check proof_asc Nat.
*)
