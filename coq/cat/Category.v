Record Category (A:Type) : Type := category
    { source    : A -> A
    ; target    : A -> A
    ; compose   : A -> A -> option A
    ; proof_ss  : forall f:A,      source (source f) = source f    
    ; proof_ts  : forall f:A,      target (source f) = source f
    ; proof_tt  : forall f:A,      target (target f) = target f
    ; proof_st  : forall f:A,      source (target f) = target f
    ; proof_dom : forall f g:A,    target f = source g <-> compose f g <> None
    ; proof_src : forall f g h:A,  compose f g = Some h -> source h = source f
    ; proof_tgt : forall f g h:A,  compose f g = Some h -> target h = target g
    ; proof_idl : forall a f:A,    a = source f -> compose a f = Some f
    ; proof_idr : forall a f:A,    a = target f -> compose f a = Some f
    ; proof_asc : forall f g h fg gh:A, compose f g = Some fg -> 
                                        compose g h = Some gh -> 
                                        compose f gh = compose fg h
    }
    .

(* implicit type argument *)
Arguments category  {A} _ _ _ _ _ _ _ _ _ _ _ _ _ .
Arguments source    {A} _ _.
Arguments target    {A} _ _.
Arguments compose   {A} _ _ _.
Arguments proof_ss  {A} _ _.
Arguments proof_ts  {A} _ _.
Arguments proof_tt  {A} _ _.
Arguments proof_st  {A} _ _.
Arguments proof_dom {A} _ _ _.
Arguments proof_src {A} _ _ _ _ _.
Arguments proof_tgt {A} _ _ _ _ _.
Arguments proof_idl {A} _ _ _ _.
Arguments proof_idr {A} _ _ _ _.
Arguments proof_asc {A} _ _ _ _ _ _ _ _.

Axiom Axiom_Category_equal : forall (A:Type) (c c':Category A),
    (forall f:A, source c f = source c' f) ->
    (forall f:A, target c f = target c' f) ->
    (forall f g:A, compose c f g = compose c' f g) -> c = c'. 




