Record Category2 (Obj Mor:Type) : Type := category2
    { dom       : Mor -> Obj
    ; cod       : Mor -> Obj
    ; compose2  : Mor -> Mor -> option Mor
    ; id        : Obj -> Mor
    ; proof_sid : forall a:Obj, dom (id a) = a
    ; proof_tid : forall a:Obj, cod (id a) = a
    ; proof_dom2: forall f g:Mor, cod f = dom g <-> compose2 f g <> None
    ; proof_src2: forall f g h: Mor, compose2 f g = Some h -> dom h = dom f
    ; proof_tgt2: forall f g h: Mor, compose2 f g = Some h -> cod h = cod g
    ; proof_idl2: forall (a:Obj) (f:Mor), a = dom f -> compose2 (id a) f = Some f
    ; proof_idr2: forall (a:Obj) (f:Mor), a = cod f -> compose2 f (id a) = Some f
    ; proof_asc2: forall f g h fg gh: Mor,    compose2 f g = Some fg ->
                                              compose2 g h = Some gh ->
                                              compose2 f gh = compose2 fg h
    }
    .

(* implicit type argument *)
Arguments category2 {Obj} {Mor} _ _ _ _ _ _ _ _ _ _ _ _.
Arguments dom {Obj} {Mor} _ _.
Arguments cod {Obj} {Mor} _ _.
Arguments compose2 {Obj} {Mor} _ _ _.
Arguments id {Obj} {Mor} _ _.
Arguments proof_sid {Obj} {Mor} _ _.
Arguments proof_tid {Obj} {Mor} _ _.
Arguments proof_dom2 {Obj} {Mor} _ _ _.
Arguments proof_src2 {Obj} {Mor} _ _ _ _ _.
Arguments proof_tgt2 {Obj} {Mor} _ _ _ _ _.
Arguments proof_idl2 {Obj} {Mor} _ _ _ _.
Arguments proof_idr2 {Obj} {Mor} _ _ _ _.
Arguments proof_asc2 {Obj} {Mor} _ _ _ _ _ _ _ _.



Lemma id_injective (Obj Mor:Type) (c:Category2 Obj Mor) : forall a b: Obj,
    id c a = id c b -> a = b.
Proof.
    intros a b H. 
    rewrite <- (proof_sid c) with (a:=b). 
    rewrite <- (proof_sid c) with (a:=a).
    rewrite H. reflexivity.
Qed.

Arguments id_injective {Obj} {Mor} _ _ _ _.



