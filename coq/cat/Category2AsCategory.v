Require Import Category2.
Require Import Category.

(* given a category2, we define the data necessary to create a category *)

Definition source_ (Obj Mor:Type) (c:Category2 Obj Mor) (f:Mor) : Mor := 
    id c (dom c f). 

Definition target_ (Obj Mor:Type) (c:Category2 Obj Mor) (f:Mor) : Mor := 
    id c (cod c f). 

Definition compose_ (Obj Mor:Type) (c:Category2 Obj Mor) (f g:Mor) : option Mor :=
    compose2 c f g.

Arguments source_  {Obj} {Mor} _ _.
Arguments target_  {Obj} {Mor} _ _.
Arguments compose_ {Obj} {Mor} _ _ _.

Definition proof_ss_ (Obj Mor:Type) (c:Category2 Obj Mor) : forall f:Mor,
    source_ c (source_ c f) = source_ c f.
Proof. 
    intros f. unfold source_. rewrite (proof_sid c). reflexivity.
Qed.

Definition proof_ts_ (Obj Mor:Type) (c:Category2 Obj Mor) : forall f:Mor,
    target_ c (source_ c f) = source_ c f.
Proof. 
    intros f. unfold target_, source_. rewrite (proof_tid c). reflexivity.
Qed.

Definition proof_tt_ (Obj Mor:Type) (c:Category2 Obj Mor) : forall f:Mor,
    target_ c (target_ c f) = target_ c f.
Proof. 
    intros f. unfold target_. rewrite (proof_tid c). reflexivity.
Qed.

Definition proof_st_ (Obj Mor:Type) (c:Category2 Obj Mor) : forall f:Mor,
    source_ c (target_ c f) = target_ c f.
Proof. 
    intros f. unfold target_, source_. rewrite (proof_sid c). reflexivity.
Qed.

Definition proof_dom_ (Obj Mor:Type) (c:Category2 Obj Mor) : forall f g: Mor,
    target_ c f = source_ c g <-> compose_ c f g <> None.
Proof.
    unfold source_, target_, compose_. split.
    - intros H. apply (proof_dom2 c). apply (id_injective c). exact H.
    - intros H. assert (cod c f = dom c g) as H'. 
      { apply (proof_dom2 c). exact H. }
      rewrite H'. reflexivity.
Qed.

Definition proof_src_ (Obj Mor:Type) (c:Category2 Obj Mor) : forall f g h: Mor,
    compose_ c f g = Some h -> source_ c h = source_ c f.
Proof.
    intros f g h H. unfold source_. unfold compose_ in H. 
    apply (proof_src2 c) in H. rewrite H. reflexivity.
Qed.

Definition proof_tgt_ (Obj Mor:Type) (c:Category2 Obj Mor) : forall f g h: Mor,
    compose_ c f g = Some h -> target_ c h = target_ c g.
Proof.
    intros f g h H. unfold target_. unfold compose_ in H. 
    apply (proof_tgt2 c) in H. rewrite H. reflexivity.
Qed.

Definition proof_idl_ (Obj Mor:Type) (c:Category2 Obj Mor) : forall a f: Mor,
    a = source_ c f -> compose_ c a f = Some f.
Proof.
    intros a f H. unfold compose_. unfold source_ in H. rewrite H.
    apply (proof_idl2 c). reflexivity.
Qed.


Definition proof_idr_ (Obj Mor:Type) (c:Category2 Obj Mor) : forall a f: Mor,
    a = target_ c f -> compose_ c f a = Some f.
Proof.
    intros a f H. unfold compose_. unfold target_ in H. rewrite H.
    apply (proof_idr2 c). reflexivity.
Qed.


Definition proof_asc_ (Obj Mor:Type)(c:Category2 Obj Mor):forall f g h fg gh:Mor,
    compose_ c f g = Some fg -> 
    compose_ c g h = Some gh -> 
    compose_ c f gh = compose_ c fg h.
Proof. unfold compose_. exact (proof_asc2 c). Qed.


Definition toCategory (Obj Mor:Type)(c:Category2 Obj Mor):Category Mor := category
    (source_            c)
    (target_            c)
    (compose_           c)
    (proof_ss_  Obj Mor c)
    (proof_ts_  Obj Mor c)
    (proof_tt_  Obj Mor c)
    (proof_st_  Obj Mor c)
    (proof_dom_ Obj Mor c)
    (proof_src_ Obj Mor c)
    (proof_tgt_ Obj Mor c)
    (proof_idl_ Obj Mor c)
    (proof_idr_ Obj Mor c)
    (proof_asc_ Obj Mor c) .

Arguments toCategory {Obj} {Mor} _.

