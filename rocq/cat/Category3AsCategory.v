Require Import Category3.
Require Import Category.

(* given a Category3, we define the data necessary to create a Category *)

Definition source_   (c:Category3) (f:A3 c) : A3 c := source3 c f.
Definition target_   (c:Category3) (f:A3 c) : A3 c := target3 c f.
Definition compose_  (c:Category3) (f g:A3 c) : option (A3 c) := compose3 c f g.

Definition proof_ss_ (c:Category3) : forall (f:A3 c), 
    source_ c (source_ c f) = source_ c f.
Proof. apply (proof_ss3 c). Qed.

Definition proof_ts_ (c:Category3) : forall (f:A3 c), 
    target_ c (source_ c f) = source_ c f.
Proof. apply (proof_ts3 c). Qed.

Definition proof_tt_ (c:Category3) : forall (f:A3 c), 
    target_ c (target_ c f) = target_ c f.
Proof. apply (proof_tt3 c). Qed.

Definition proof_st_ (c:Category3) : forall (f:A3 c), 
    source_ c (target_ c f) = target_ c f.
Proof. apply (proof_st3 c). Qed.

Definition proof_dom_ (c:Category3): forall (f g: A3 c),
    target_ c f = source_ c g <-> compose_ c f g <> None.
Proof. apply (proof_dom3 c). Qed. 

Definition proof_src_ (c:Category3): forall (f g h: A3 c),
    compose_ c f g = Some h -> source_ c h = source_ c f.
Proof. apply (proof_src3 c). Qed. 

Definition proof_tgt_ (c:Category3): forall (f g h: A3 c),
    compose_ c f g = Some h -> target_ c h = target_ c g.
Proof. apply (proof_tgt3 c). Qed. 

Definition proof_idl_ (c:Category3): forall (a f: A3 c),
    a = source_ c f -> compose_ c a f = Some f.
Proof. apply (proof_idl3 c). Qed. 

Definition proof_idr_ (c:Category3): forall (a f: A3 c),
    a = target_ c f -> compose_ c f a = Some f.
Proof. apply (proof_idr3 c). Qed. 

Definition proof_asc_ (c:Category3): forall (f g h fg gh: A3 c),
    compose_ c f g = Some fg ->
    compose_ c g h = Some gh ->
    compose_ c f gh = compose_ c fg h.
Proof. apply (proof_asc3 c). Qed. 


Definition toCategory (c:Category3):Category (A3 c) := category
    (source_            c)
    (target_            c)
    (compose_           c)
    (proof_ss_          c)
    (proof_ts_          c)
    (proof_tt_          c)
    (proof_st_          c)
    (proof_dom_         c)
    (proof_src_         c)
    (proof_tgt_         c)
    (proof_idl_         c)
    (proof_idr_         c)
    (proof_asc_         c) .




