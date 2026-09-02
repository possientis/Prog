Require Import Category4.
Require Import Category2.

(* given a Category4, we define the data necessary to create a Category2 *)

Definition dom_ (c:Category4) (f:Mor4 c) : Obj4 c := dom4 c f.
Definition cod_ (c:Category4) (f:Mor4 c) : Obj4 c := cod4 c f.
Definition compose2_ (c:Category4) (f g:Mor4 c) : option (Mor4 c) := compose4 c f g.
Definition id_ (c:Category4) (a:Obj4 c) : Mor4 c := id4 c a.

Definition proof_sid_ (c:Category4) : forall (a:Obj4 c), dom_ c (id_ c a) = a.
Proof. apply (proof_sid4 c). Qed.

Definition proof_tid_ (c:Category4) : forall (a:Obj4 c), cod_ c (id_ c a) = a.
Proof. apply (proof_tid4 c). Qed.


Definition proof_dom2_ (c:Category4) : forall (f g:Mor4 c),
    cod_ c f = dom_ c g <-> compose2_ c f g <> None.
Proof. apply (proof_dom4 c). Qed.


Definition proof_src2_ (c:Category4) : forall (f g h:Mor4 c),
    compose2_ c f g = Some h -> dom_ c h = dom_ c f.
Proof. apply (proof_src4 c). Qed.

Definition proof_tgt2_ (c:Category4) : forall (f g h:Mor4 c),
    compose2_ c f g = Some h -> cod_ c h = cod_ c g.
Proof. apply (proof_tgt4 c). Qed.

Definition proof_idl2_ (c:Category4) : forall (a:Obj4 c) (f:Mor4 c), 
    a = dom_ c f -> compose2_ c (id_ c a) f = Some f.
Proof. apply (proof_idl4 c). Qed.

Definition proof_idr2_ (c:Category4) : forall (a:Obj4 c) (f:Mor4 c), 
    a = cod_ c f -> compose2_ c f (id_ c a) = Some f.
Proof. apply (proof_idr4 c). Qed.

Definition proof_asc2_ (c:Category4) : forall (f g h fg gh:Mor4 c), 
    compose2_ c f g  = Some fg ->
    compose2_ c g h  = Some gh ->
    compose2_ c f gh = compose2_ c fg h.
Proof. apply (proof_asc4 c). Qed.


Definition toCategory2 (c:Category4):Category2 (Obj4 c) (Mor4 c) := category2
    (dom_               c)
    (cod_               c)
    (compose2_          c)
    (id_                c)
    (proof_sid_         c)
    (proof_tid_         c)
    (proof_dom2_        c)
    (proof_src2_        c)
    (proof_tgt2_        c)
    (proof_idl2_        c)
    (proof_idr2_        c)
    (proof_asc2_        c) . 



