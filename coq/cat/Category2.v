Record Category2 (Obj Mor:Type) : Type := category
    {   dom     : Mor -> Obj
    ;   cod     : Mor -> Obj
    ;   compose : Mor -> Mor -> option Mor
    ;   id      : Obj -> Mor
    ;   proof_dom : forall f g:Mor, cod f = dom g <-> compose f g <> None
    ;   proof_src : forall f g h: Mor, compose f g = Some h -> dom h = dom f
    ;   proof_tgt : forall f g h: Mor, compose f g = Some h -> cod h = cod g
    ;   proof_idl : forall (a:Obj) (f:Mor), a = dom f -> compose (id a) f = Some f
    ;   proof_idr : forall (a:Obj) (f:Mor), a = cod f -> compose f (id a) = Some f
    ;   proof_asc : forall f g h fg gh: Mor,    compose f g = Some fg ->
                                                compose g h = Some gh ->
                                                compose f gh = compose fg h
    }
    .


(* implicit type argument *)
Arguments category {Obj} {Mor} _ _ _ _ _ _ _ _ _ _.
Arguments dom {Obj} {Mor} _ _.
Arguments cod {Obj} {Mor} _ _.
Arguments compose {Obj} {Mor} _ _ _.
Arguments id {Obj} {Mor} _ _.

