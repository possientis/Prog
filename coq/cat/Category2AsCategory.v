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
    - intros H. assert (cod c f = dom c g) as H'. { apply (proof_dom2 c). exact H. }
      rewrite H'. reflexivity.
Qed.




