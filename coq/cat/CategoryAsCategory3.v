Require Import Category.
Require Import Category3.

(* given a Category we define the data necessary to create a Category3 *)

Definition A3_ (A:Type) (c:Category A) : Type := A.
Arguments A3_ {A} _.


Definition source3_    (A:Type) (c:Category A) (x: A3_ c) : A3_ c := source c x.
Definition target3_    (A:Type) (c:Category A) (x: A3_ c) : A3_ c := target c x.
Definition compose3_   (A:Type) (c:Category A) (x y: A3_ c) : option (A3_ c) := 
    compose c x y.

Arguments source3_  {A} _ _.
Arguments target3_  {A} _ _.
Arguments compose3_ {A} _ _ _.

Definition proof_ss3_  (A:Type) (c:Category A) : forall (f:A3_ c),
    source3_ c (source3_ c f) = source3_ c f.
Proof. apply (proof_ss c). Qed.


Definition proof_ts3_  (A:Type) (c:Category A) : forall (f:A3_ c),
    target3_ c (source3_ c f) = source3_ c f.
Proof. apply (proof_ts c). Qed.


Definition proof_tt3_  (A:Type) (c:Category A) : forall (f:A3_ c),
    target3_ c (target3_ c f) = target3_ c f.
Proof. apply (proof_tt c). Qed.


Definition proof_st3_  (A:Type) (c:Category A) : forall (f:A3_ c),
    source3_ c (target3_ c f) = target3_ c f.
Proof. apply (proof_st c). Qed.


Definition proof_dom3_  (A:Type) (c:Category A) : forall (f g:A3_ c),
    target3_ c f = source3_ c g <-> compose3_ c f g <> None.
Proof. apply (proof_dom c). Qed.


Definition proof_src3_  (A:Type) (c:Category A) : forall (f g h:A3_ c),
    compose3_ c f g = Some h -> source3_ c h = source3_ c f.
Proof. apply (proof_src c). Qed.


Definition proof_tgt3_  (A:Type) (c:Category A) : forall (f g h:A3_ c),
    compose3_ c f g = Some h -> target3_ c h = target3_ c g.
Proof. apply (proof_tgt c). Qed.


Definition proof_idl3_  (A:Type) (c:Category A) : forall (a f:A3_ c),
    a = source3_ c f -> compose3_ c a f = Some f.
Proof. apply (proof_idl c). Qed.


Definition proof_idr3_  (A:Type) (c:Category A) : forall (a f:A3_ c),
    a = target3_ c f -> compose3_ c f a = Some f.
Proof. apply (proof_idr c). Qed.


Definition proof_asc3_  (A:Type) (c:Category A) : forall (f g h fg gh:A3_ c),
    compose3_ c f g  = Some fg ->
    compose3_ c g h  = Some gh ->
    compose3_ c f gh = compose3_ c fg h. 
Proof. apply (proof_asc c). Qed.

Definition toCategory3 (A:Type) (c:Category A) : Category3 := category3
    (A3_                c)
    (source3_           c)
    (target3_           c)
    (compose3_          c)
    (proof_ss3_     A   c)
    (proof_ts3_     A   c)
    (proof_tt3_     A   c)
    (proof_st3_     A   c)
    (proof_dom3_    A   c)
    (proof_src3_    A   c)
    (proof_tgt3_    A   c)
    (proof_idl3_    A   c)
    (proof_idr3_    A   c)
    (proof_asc3_    A   c).

Arguments toCategory3 {A} _.


