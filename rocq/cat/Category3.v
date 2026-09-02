Record Category3 : Type := category3
    { A3         : Type 
    ; source3    : A3 -> A3
    ; target3    : A3 -> A3
    ; compose3   : A3 -> A3 -> option A3
    ; proof_ss3  : forall f:A3,     source3 (source3 f) = source3 f    
    ; proof_ts3  : forall f:A3,     target3 (source3 f) = source3 f
    ; proof_tt3  : forall f:A3,     target3 (target3 f) = target3 f
    ; proof_st3  : forall f:A3,     source3 (target3 f) = target3 f
    ; proof_dom3 : forall f g:A3,   target3 f = source3 g <-> compose3 f g <> None
    ; proof_src3 : forall f g h:A3, compose3 f g = Some h -> source3 h = source3 f
    ; proof_tgt3 : forall f g h:A3, compose3 f g = Some h -> target3 h = target3 g
    ; proof_idl3 : forall a f:A3,   a = source3 f -> compose3 a f = Some f
    ; proof_idr3 : forall a f:A3,   a = target3 f -> compose3 f a = Some f
    ; proof_asc3 : forall f g h fg gh:A3, compose3 f g = Some fg -> 
                                          compose3 g h = Some gh -> 
                                          compose3 f gh = compose3 fg h
    }
    .



