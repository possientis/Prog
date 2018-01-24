Require Import Option.

Record Category4 : Type := category4
    { Obj4      : Type
    ; Mor4      : Type  
    ; dom4      : Mor4 -> Obj4
    ; cod4      : Mor4 -> Obj4
    ; compose4  : Mor4 -> Mor4 -> option Mor4
    ; id4       : Obj4 -> Mor4
    ; proof_sid4: forall a:Obj4, dom4 (id4 a) = a
    ; proof_tid4: forall a:Obj4, cod4 (id4 a) = a
    ; proof_dom4: forall f g:Mor4, cod4 f = dom4 g <-> compose4 f g <> None
    ; proof_src4: forall f g h: Mor4, compose4 f g = Some h -> dom4 h = dom4 f
    ; proof_tgt4: forall f g h: Mor4, compose4 f g = Some h -> cod4 h = cod4 g
    ; proof_idl4: forall (a:Obj4) (f:Mor4),a = dom4 f -> compose4 (id4 a) f = Some f
    ; proof_idr4: forall (a:Obj4) (f:Mor4),a = cod4 f -> compose4 f (id4 a) = Some f
    ; proof_asc4: forall f g h fg gh: Mor4,   compose4 f g = Some fg ->
                                              compose4 g h = Some gh ->
                                              compose4 f gh = compose4 fg h
    }
    .

(* proof_dom4 is an equivalence, we need implication (function) -> *)
Lemma proof_dom4' : forall (C:Category4) (f g:Mor4 C),
    cod4 C f = dom4 C g -> compose4 C f g <> None.
Proof.
    intros C f g H. apply (proof_dom4 C). exact H.
Qed.

Arguments proof_dom4' {C} _ _ _ _.
 
Definition compose4' (C:Category4)(f g:Mor4 C)(p:cod4 C f = dom4 C g): Mor4 C :=
    fromOption (compose4 C f g) (proof_dom4' f g p). 

Arguments compose4' {C} _ _ _.

Lemma compose4'_correct:forall (C:Category4)(f g:Mor4 C)(p:cod4 C f = dom4 C g),
    compose4 C f g = Some (compose4' f g p).
Proof.
    intros C f g p. unfold compose4'. apply fromOption_correct.
Qed.

Lemma compose4'_dom:forall (C:Category4)(f g:Mor4 C)(p:cod4 C f = dom4 C g),
    dom4 C (compose4' f g p) = dom4 C f.
Proof.
    intros C f g p. apply (proof_src4 C f g (compose4' f g p)). 
    apply compose4'_correct.
Qed.
    
Lemma compose4'_cod:forall (C:Category4)(f g:Mor4 C)(p:cod4 C f = dom4 C g),
    cod4 C (compose4' f g p) = cod4 C g.
Proof.
    intros C f g p. apply (proof_tgt4 C f g (compose4' f g p)). 
    apply compose4'_correct.
Qed.
 
Lemma compose4'_idl:forall (C:Category4)(a:Obj4 C)(f:Mor4 C),
    forall (p:cod4 C (id4 C a) = dom4 C f), compose4' (id4 C a) f p = f.
Proof.
    intros C a f p. unfold compose4'. assert (a = dom4 C f) as q.
    { rewrite (proof_tid4 C a) in p. exact p. } 
    remember (proof_dom4' (id4 C a) f p) as r eqn:H. clear H.
    revert r. rewrite (proof_idl4 C a f q).
    intros r. symmetry. apply fromOption_Some.
Qed.

Lemma compose4'_idr:forall (C:Category4)(a:Obj4 C)(f:Mor4 C),
    forall (p:cod4 C f = dom4 C (id4 C a)), compose4' f (id4 C a) p = f.

Proof.
    intros C a f p. unfold compose4'. assert (cod4 C f = a) as q.
    { rewrite (proof_sid4 C a) in p. exact p. } 
    remember (proof_dom4' f (id4 C a) p) as r eqn:H. clear H.
    revert r. symmetry in q. rewrite (proof_idr4 C a f q).
    intros r. symmetry. apply fromOption_Some.
Qed.

