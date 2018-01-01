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


