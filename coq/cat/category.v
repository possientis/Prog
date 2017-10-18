Record Category (A:Type) : Type := category
    {   source : A -> A
    ;   target : A -> A
    ;   product: A -> A -> option A
    ;   proof_ss : forall f:A, source (source f) = source f    
    ;   proof_ts : forall f:A, target (source f) = source f
    ;   proof_tt : forall f:A, target (target f) = target f
    ;   proof_st : forall f:A, source (target f) = target f
    ;   proof_dom: forall f g:A, target f = source g <-> product f g <> None
    ;   proof_src: forall f g h:A, product f g = Some h -> source h = source f
    ;   proof_tgt: forall f g h:A, product f g = Some h -> target h = target g
    ;   proof_idl: forall a f:A, 
            a = source a -> 
            a = target a -> 
            a = source f -> 
            product a f = Some f
    ;   proof_idr: forall a f:A,
            a = source a -> 
            a = target a -> 
            a = target f -> 
            product f a = Some f
    ;   proof_asc: 
            forall f g h fg gh:A, 
            product f g = Some fg -> 
            product g h = Some gh -> 
            product fg h = product f gh
    }
    .


